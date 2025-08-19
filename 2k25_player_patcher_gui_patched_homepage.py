"""
2K25 Player Patcher GUI
-----------------------

This script implements a simple editor for NBA 2K25 player data.  It
leverages Windows API calls via `ctypes` to locate the running game,
enumerate player records in memory and edit basic fields such as first name,
last name and face ID.  If the game is not running or the process cannot be
opened, the interface will show no players or teams.

**Disclaimer**: This tool is intended for offline use only.  Editing
in‑memory data could violate NBA 2K25’s terms of service if used in online
modes.  Use at your own risk.

Example usage:

```cmd
python 2k25_player_patcher_gui.py
```

You will be presented with a window containing a side bar with “Home” and
“Players” options.  The Home page displays whether NBA 2K25 is currently
running and the application version.  The Players page scans for players
in memory, groups them by team and allows editing of names and face IDs.  A
full editor window with placeholder tabs is available for future extensions.
"""

import os
import sys
import threading
import struct
import ctypes
from ctypes import wintypes
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from typing import Dict
import random
import tempfile
import urllib.request
import urllib.parse
import io
# Offsets loader
try:
    import offsets_reader
except Exception:
    offsets_reader = None

###############################################################################
# Configuration constants extracted from the Cheat Engine table (Patch 4)
#
# These values originate from the “Player Data Patch 4.txt” file uploaded by
# the user.  They define the location of the player table relative to the
# NBA2K25.exe module and the offsets of various fields inside each player
# record.  If a game update moves or changes this layout, update these
# values accordingly.

MODULE_NAME = "NBA2K25.exe"
PLAYER_TABLE_RVA = 0x07E52998  # relative virtual address of the player table
PLAYER_STRIDE = 0x448  # size of each player record (1096 bytes)

# Candidate pointer chains for resolving the start of the player table.  The
# game changes its internal pointer layout between patches, so we list
# several known chains here.  Each tuple is `(rva_offset, final_offset, extra_deref)`.
#   * ``rva_offset`` is added to the module base to obtain the first pointer.
#   * ``final_offset`` is added after the pointer chain has been resolved to
#     arrive at the first player record.  See ``_resolve_player_base`` for
#     details.
#   * ``extra_deref`` indicates whether to perform an additional pointer
#     dereference before adding ``final_offset``.  Some patches store the
#     table pointer one level deeper (e.g. ``[ [base+rva] ]``) instead of
#     directly at ``[base+rva]``.
PLAYER_PTR_CHAINS: list[tuple[int, int, bool]] = [
    # Patch 4 (10.18.24): [[module_base + 0x07E39430] + 0x448*0] + 0x18
    (0x07E39430, 0x18, True),
    # Edit Player table (10.18.24): [module_base + 0x06E14E48] + 0x148
    (0x06E14E48, 0x148, False),
    # Static RVA (Patch 4 older builds): module_base + 0x07E52998
    (PLAYER_TABLE_RVA, 0x0, False),
    # Legacy offsets (e.g. from early patch data): module_base + 0x07E5DD88
    # This entry relies on the overrides loader to update PLAYER_TABLE_RVA
    # if necessary.  We still include it here with no extra dereference.
    (0x07E5DD88, 0x0, False),
]

# Offsets within the player record
OFF_LAST_NAME = 0x000  # last name at +0 (20 UTF‑16 chars)
OFF_FIRST_NAME = 0x028  # first name at +0x28 (20 UTF‑16 chars)
OFF_FACE_ID = 0x114  # face ID (4 bytes)
OFF_TEAM_PTR = 0x060  # pointer to team structure
OFF_TEAM_NAME = 0x2D4  # offset within team structure to team name

# Other constants
# Maximum number of players to scan when reading the in‑memory player table.
# NBA 2K25 allocates space for thousands of players (including historic teams
# and draft classes).  To ensure we enumerate all entries without excessive
# overhead, this constant is tuned to 6,000.  Adjust this value if you
# need to scan more or fewer players.
MAX_PLAYERS = 6000
NAME_MAX_CHARS = 20  # maximum characters in name fields
APP_VERSION = "0.1"  # displayed application version

# -----------------------------------------------------------------------------
# Rating scaling constants
#
# NBA 2K25 stores player attributes in bitfields that are later mapped to
# ratings shown to the user.  Through observation of the in‑game code it
# appears that the theoretical maximum rating used internally is 110 even
# though the UI caps values at 99.  To ensure that imported ratings map
# proportionally across the full bitfield range regardless of length, we
# expose two constants:
#
#   * RATING_MIN: the minimum rating shown in game.  Typically 25.
#   * RATING_MAX_DISPLAY: the maximum rating exposed in the UI (99).
#   * RATING_MAX_TRUE: the maximum rating used internally (110).  Raw
#     bitfield values corresponding to 110 will appear as 99 in the UI
#     but preserve the correct scale when computing intermediate values.

RATING_MIN = 25
RATING_MAX_DISPLAY = 99
RATING_MAX_TRUE = 110

# ----------------------------------------------------------------------------
# Attribute storage mode:
# - 'direct': raw byte stores the true 25..110 value directly (legacy assumption)
# - 'scale' : raw uses 0..max_raw (e.g., 0..255) linearly mapped to 25..110
ATTR_STORAGE_MODE = 'scale'

# ----------------------------------------------------------------------------
# Badge level definitions
#
# Each badge stored in the player record occupies a three‑bit field (values
# 0–7).  In practice, NBA 2K uses only the lower five values: 0 = no
# badge, 1 = Bronze, 2 = Silver, 3 = Gold and 4 = Hall of Fame.  Values
# above 4 have no effect in game.  When presenting badges in the UI we
# expose only these five levels.  The lists below provide the names and
# corresponding integer values used throughout the code.
BADGE_LEVEL_NAMES: list[str] = [
    "None",
    "Bronze",
    "Silver",
    "Gold",
    "Hall of Fame",
]
# Reverse lookup from name to value for convenience
BADGE_NAME_TO_VALUE: dict[str, int] = {
    name: idx for idx, name in enumerate(BADGE_LEVEL_NAMES)
}

# ----------------------------------------------------------------------------
# Rating conversion helpers
#
# The 2K25 game stores player ratings as raw bitfields of varying lengths.
# To present intuitive 25–110 scales to users and convert back when saving,
# we define helper functions below.  These functions map a raw integer
# (0..2^length-1) to a rating (25..99) and vice versa.  Most attribute fields
# in NBA 2K25 store the true 25–110 rating directly in a full byte.  For those
# cases the conversion is effectively a clamp from 25–110 down to the visible
# 25–99 range.  If a field’s bit width is smaller than needed to represent the
# entire 25–110 range, we fall back to a proportional mapping across that
# range.  Ratings outside the expected range are clamped.


def convert_raw_to_rating(raw: int, length: int) -> int:
    """Decode raw bitfield to true 25..110 rating. Honors ATTR_STORAGE_MODE.
    - 'direct': treat raw as the true rating when field is wide enough
    - 'scale' : map 0..max_raw linearly to 25..110
    """
    try:
        max_raw = (1 << length) - 1
        if max_raw <= 0:
            return RATING_MIN
        if ATTR_STORAGE_MODE == 'direct' and max_raw >= RATING_MAX_TRUE:
            rating = int(raw)
        else:
            rating = RATING_MIN + (int(raw) / max_raw) * (RATING_MAX_TRUE - RATING_MIN)
        if rating < RATING_MIN:
            rating = RATING_MIN
        elif rating > RATING_MAX_TRUE:
            rating = RATING_MAX_TRUE
        return int(round(rating))
    except Exception:
        return RATING_MIN

def convert_rating_to_raw(rating: float, length: int) -> int:
    """Encode 25..110 rating into bitfield. Honors ATTR_STORAGE_MODE."""
    try:
        max_raw = (1 << length) - 1
        if max_raw <= 0:
            return 0
        r = float(rating)
        if r < RATING_MIN:
            r = RATING_MIN
        elif r > RATING_MAX_TRUE:
            r = RATING_MAX_TRUE
        if ATTR_STORAGE_MODE == 'direct' and max_raw >= RATING_MAX_TRUE:
            raw_val = int(round(r))
        else:
            fraction = (r - RATING_MIN) / (RATING_MAX_TRUE - RATING_MIN)
            if fraction < 0.0:
                fraction = 0.0
            elif fraction > 1.0:
                fraction = 1.0
            raw_val = int(round(fraction * max_raw))
        if raw_val < 0:
            raw_val = 0
        elif raw_val > max_raw:
            raw_val = max_raw
        return raw_val
    except Exception:
        return 0

def convert_tendency_raw_to_rating(raw: int, length: int) -> int:
    """
    Convert a raw bitfield value into a 0–100 tendency rating.  When the
    game stores tendency values in a bitfield of ``length`` bits, the
    minimum raw value represents a rating of 0 and the maximum raw value
    represents a rating of 100.  Intermediate values are scaled linearly.

    Parameters
    ----------
    raw : int
        The integer stored in the bit field.
    length : int
        Number of bits in the field; determines the maximum representable
        raw value.

    Returns
    -------
    int
        Rating on the 0–100 scale, rounded to the nearest integer and
        clamped to 0..100.
    """
    try:
        max_raw = (1 << length) - 1
        if max_raw <= 0:
            return 0
        # Proportional mapping: raw 0..max_raw maps to 0..100
        rating = (raw / max_raw) * 100.0
        if rating < 0.0:
            rating = 0.0
        elif rating > 100.0:
            rating = 100.0
        return int(round(rating))
    except Exception:
        return 0


def convert_rating_to_tendency_raw(rating: float, length: int) -> int:
    """
    Convert a 0–100 tendency rating into a raw bitfield value.  Tendency
    ratings may be specified by the user or imported from a file; this
    function clamps them to the valid 0..100 range and scales them into
    the 0..(2^length−1) raw range.

    Parameters
    ----------
    rating : float
        The desired rating on the 0–100 scale.
    length : int
        Number of bits in the field; determines the maximum representable
        raw value.

    Returns
    -------
    int
        Raw bitfield value corresponding to the rating.
    """
    try:
        max_raw = (1 << length) - 1
        if max_raw <= 0:
            return 0
        r = float(rating)
        if r < 0.0:
            r = 0.0
        elif r > 100.0:
            r = 100.0
        fraction = r / 100.0
        if fraction < 0.0:
            fraction = 0.0
        elif fraction > 1.0:
            fraction = 1.0
        raw_val = round(fraction * max_raw)
        if raw_val < 0:
            raw_val = 0
        elif raw_val > max_raw:
            raw_val = max_raw
        return int(raw_val)
    except Exception:
        return 0


# ----------------------------------------------------------------------------
# Extra categories not defined in the unified offsets
#
# Some high‑level features (e.g. contract details) may not be included
# in the unified offsets file but are known from the cheat tables
# provided by the user.  We define them here so that the editor can expose
# additional tabs when loading categories.  Each entry contains a list of
# field definitions with the following keys:
#
#     name: Human‑readable label
#     offset: Byte offset within the player record (as a hex string)
#     startBit: Starting bit position within the byte at ``offset``
#     length: Number of bits
#     values (optional): A list of display strings corresponding to the
#                        integer stored in the field.  If provided, a
#                        combobox is used instead of a numeric spinbox.

EXTRA_CATEGORIES: dict[str, list[dict]] = {
    "Contract": [
        {
            "name": "Original Contract Length",
            "offset": "0x302",
            "startBit": 4,
            "length": 3,
            "values": [
                "0 years",
                "1 year",
                "2 years",
                "3 years",
                "4 years",
                "5 years",
                "6 years",
                "7 years",
            ],
        },
        {
            "name": "Years Left",
            "offset": "0x390",
            "startBit": 0,
            "length": 5,
        },
        {
            "name": "Bird Years",
            "offset": "0x34E",
            "startBit": 6,
            "length": 5,
        },
        {
            "name": "Free Agency Type",
            "offset": "0x300",
            "startBit": 4,
            "length": 2,
            "values": [
                "Unrestricted",
                "Restricted",
                "Rookie Restricted",
            ],
        },
        {
            "name": "Option",
            "offset": "0x2FA",
            "startBit": 5,
            "length": 2,
            "values": [
                "None",
                "Team",
                "Player",
                "2 Yr Team",
            ],
        },
        {
            "name": "No Trade",
            "offset": "0x1B6",
            "startBit": 2,
            "length": 1,
            "values": [
                "No",
                "Yes",
            ],
        },
        {
            "name": "Extension Length",
            "offset": "0x30A",
            "startBit": 2,
            "length": 3,
            "values": [
                "0 years",
                "1 year",
                "2 years",
                "3 years",
                "4 years",
                "5 years",
                "6 years",
                "7 years",
            ],
        },
        {
            "name": "Extension Option",
            "offset": "0x303",
            "startBit": 6,
            "length": 2,
            "values": [
                "None",
                "Team",
                "Player",
                "2 Yr Team",
            ],
        },
        {
            "name": "Extension No Trade",
            "offset": "0x2F8",
            "startBit": 5,
            "length": 1,
            "values": [
                "No",
                "Yes",
            ],
        },
    ],
}

# ----------------------------------------------------------------------------
# Configuration for the "2K COY" auto‑import feature.
#
# The 2K COY button can automatically fetch player update tables from a
# Google Sheet.  To enable this, set ``COY_SHEET_ID`` to the ID of the
# sheet (the long string in the URL after ``/d/``) and map each roster
# category to the sheet name in ``COY_SHEET_TABS``.  When the button is
# clicked the program will download the CSV export of each sheet and
# apply the updates.  If you do not wish to use auto‑download, leave
# ``COY_SHEET_ID`` empty and the button will prompt you for files.

# ID of the Google Sheet containing the COY tables.  If blank, the
# program will fall back to asking the user for files.
COY_SHEET_ID: str = "1pxWukEO6oOofSZdPKyu--R_8EyvHOflArT2tJFBzzzo"

# Mapping of roster categories to the names of sheets inside the Google
# Sheet.  The keys must match the category names used by
# ``PlayerDataModel.import_all`` ("Attributes", "Tendencies", "Durability"),
# and the values should match the tab names in the sheet exactly.  You
# can adjust these if your sheet uses different tab labels.
COY_SHEET_TABS: dict[str, str] = {
    "Attributes": "Attributes",
    "Tendencies": "Tendencies",
    "Durability": "Durabilities",
}

# Constants for the team table and pointer chains.  These values were
# initially derived from the Cheat Engine "Team Data" table for Patch 4,
# but NBA 2K25 has been observed to change them across updates.  To
# accommodate multiple patches, we define candidate pointer chains and
# allow the code to try each one until a valid list of team names is
# produced.  See the documentation for ``_resolve_team_base_ptr`` for
# details on how these chains are resolved.

# Each team record is 0x654 bytes long (1620 bytes).  Within each record,
# the first 16 or so 8‑byte entries are pointers to players on that
# team's roster; the team name string is located at offset 0x2D4 (for
# at least the patches tested so far).

# Length of a team record in bytes.  In NBA 2K25 Patch 4 each team record
# occupies 0x1620 (5664) bytes of memory, as documented in the unified
# offsets file and the Cheat Engine table.  Earlier versions of this
# script used a much smaller stride (0x654) which caused the roster type
# and historic year fields to be read from incorrect locations (because
# those offsets lie well beyond 0x654).  When the stride is too short,
# classic teams such as "1996‑97 Bulls" collapse into their modern
# counterparts because the year bits are never found.  Updating the
# stride to the correct 0x1620 ensures that fields like ``TEAM_TYPE_OFFSET``
# (0x12F7) and ``TEAM_YEAR_OFFSET`` (0x161A) fall within the same record.
TEAM_STRIDE = 0x1620
TEAM_NAME_OFFSET = 0x2D4  # offset to team name string (length 24)
TEAM_NAME_LENGTH = 24
# Roster type bitfield (bits 2..6) identifying NBA, historic, All-Time, etc.
TEAM_TYPE_OFFSET = 0x12F7
# Historic year bitfield (bits 3..9).  Non-zero only for historic teams.
TEAM_YEAR_OFFSET = 0x161A
# Maximum number of player pointers stored per team.  2K typically stores
# up to 20 players for NBA teams.
TEAM_PLAYER_SLOT_COUNT = 20

# Maximum number of team records to scan.  The default of 40
# only covers current NBA teams plus a handful of extras.  To
# include All‑Time, Draft Class and G‑League teams, increase this
# limit.  Setting the value too high may cause the scanner to
# attempt to read invalid memory, but modern systems can handle
# scanning 80–100 records with minimal overhead.  Adjust as
# necessary if more teams are added in future patches.
# Maximum number of team records to scan.  NBA 2K25 includes current NBA
# teams, All‑Time teams, classic teams and G‑League teams.  To capture
# rosters from all available teams (including user‑created teams), bump
# this limit to 300.  Scanning beyond the actual number of teams simply
# stops when an empty record is encountered.
MAX_TEAMS_SCAN = 300

# Candidate pointer chains for resolving the base of the team table.  Each
# tuple is `(rva_offset, final_offset, extra_deref)`.  See
# ``_resolve_team_base_ptr`` for details.
TEAM_PTR_CHAINS: list[tuple[int, int, bool]] = [
    # Patch 4: [[module_base + 0x07E39430] + 0x0] + 0x88
    (0x07E39430, 0x88, True),
    # Fallback: [module_base + 0x07E39430] + 0x0
    (0x07E39430, 0x0, False),
    # Fallback: [module_base + 0x07DFFAC0] + 0x0
    (0x07DFFAC0, 0x0, False),
]

# -----------------------------------------------------------------------------
# Definitions for editing team metadata.  These constants describe where
# various pieces of information about a team are stored within a team
# record.  The offsets and lengths were derived from the Cheat Engine
# "Team Data" table supplied by the user.  Each entry below corresponds
# to a human‑readable field name, the byte offset within the team record,
# and the maximum number of UTF‑16 characters that field can hold.  These
# definitions drive the dynamic team editor implemented in the GUI.

# Size of a team record in bytes (must match TEAM_STRIDE above)
TEAM_RECORD_SIZE = TEAM_STRIDE

# Dictionary mapping field labels to a tuple of (offset, max_chars).  The
# offsets originate from the "Team Data (10.18.24)" cheat table.  Lengths
# indicate how many UTF‑16 characters to read/write.  Feel free to add
# more entries here if you discover additional editable fields.  Unknown
# or unused fields should be omitted to avoid corrupting memory.
TEAM_FIELDS: dict[str, tuple[int, int]] = {
    "Team Name": (0x2D4, 24),  # full team name (e.g. "Golden State Warriors")
    "City Name": (0x306, 24),  # city name (e.g. "San Francisco")
    "City Short Name": (0x32A, 8),  # abbreviated city (e.g. "SF")
    "State Short Name": (0x338, 8),  # abbreviated state (e.g. "CA")
    "Arena Name": (0x158, 36),  # home arena name (e.g. "Chase Center")
    # Additional fields such as logos or nicknames could be added here if
    # their offsets and lengths are known.  For example:
    # "Logo": (0x196, 36),
}

# -----------------------------------------------------------------------------
# Unified offsets support
#
# To simplify distribution of offset information and avoid conflicting names
# between internal 2K labels and editor UI labels, this editor supports
# loading a unified offsets file.  When present, a unified file contains
# ``Base`` definitions and category lists ("Body", "Vitals", "Attributes",
# "Badges" and "Tendencies").  Field names inside these categories may be
# customized (e.g. prefixed with ``mod_``) to avoid collisions with game
# internals.  The ``UNIFIED_FILES`` tuple lists candidate filenames in
# priority order.  The loader functions below attempt to read the first
# existing file in this list before falling back.  Legacy files
# ``potion.txt`` and ``offsets.json`` are no longer consulted.

# Candidate unified offset filenames.  Place your unified offsets JSON in the
# script directory with one of these names to override the built‑in offsets.
UNIFIED_FILES = (
    "unified_offsets_mod.json",
    "unified_offsets_full.json",
    "unified_offsets_full.text",
    "unified_offsets.json",
)

# New offsets and lengths for bulk data copy operations.  These values are
# derived from the cheat table and correspond to contiguous regions of the
# player record.  They can be used to copy attributes, tendencies and
# badges from one player to another.
OFF_APPEARANCE = 0x078  # appearance block as defined in the original script
LEN_APPEARANCE = 51
OFF_ATTRIBUTES = 0x392  # attributes block (approx. 0x392 bytes into record)
LEN_ATTRIBUTES = 53
OFF_TENDENCIES = 0x3C8  # tendencies block (approx. 0x3C8 bytes into record)
LEN_TENDENCIES = 99
OFF_BADGES = 0x42A  # badges/personality block
LEN_BADGES = 19

# -----------------------------------------------------------------------------
# Import table definitions
#
# The application supports importing player data from tab- or comma-delimited
# text files.  To align the UI with commonly used spreadsheets, we define
# canonical field orders for three tables: Attributes, Tendencies and
# Durability.  These lists specify the order in which fields should appear
# in the editor and the import files.  When loading the category definitions
# from a unified offsets file, the ``_load_categories`` helper
# reorders the fields to match these lists (where possible).  Unmatched
# fields remain at the end of the list.  Synonym matching is performed
# during import via simple string normalization (see ``_normalize_name``).

# Order for the Attributes table.  These names correspond to the column
# headers in user‑provided import files.  Note: ``PLAYER_NAME`` is not a
# field in the save data; it is used as a row identifier in import files.
ATTR_IMPORT_ORDER = [
    "LAYUP",
    "STDUNK",
    "DUNK",
    "CLOSE",
    "MID",
    "3PT",
    "FT",
    "PHOOK",
    "PFADE",
    "POSTC",
    "FOUL",
    "SHOTIQ",
    "BALL",
    "SPD/BALL",
    "HANDS",
    "PASS",
    "PASS_IQ",
    "VISION",
    "OCNST",
    "ID",
    "PD",
    "STEAL",
    "BLOCK",
    "OREB",
    "DREB",
    "HELPIQ",
    "PSPER",
    "DCNST",
    "SPEED",
    "AGIL",
    "STR",
    "VERT",
    "STAM",
    "INTNGBL",
    "HSTL",
    "DUR",
    "POT",
]

# Order for the Durability table.  These headers correspond to various
# body part durability ratings.  Not every header may map directly to a
# field in the offset map; unmatched entries will be ignored.
DUR_IMPORT_ORDER = [
    "Back",
    "Head",
    "Left Ankle",
    "Left Elbow",
    "Left Foot",
    "Left Hip",
    "Left Knee",
    "Left Shoulder",
    "Neck",
    "Right Ankle",
    "Right Elbow",
    "Right Foot",
    "Right Hip",
    "Right Knee",
    "Right Shoulder",
    "miscellaneous",
]

# Order for the Tendencies table.  These column names are taken directly
# from the sample provided by the user.  They will be normalized and
# matched against the field names defined in the "Tendencies" category of
# the offset map.  Unmatched fields remain in their original order.
TEND_IMPORT_ORDER = [
    "T/SHOT",
    "T/TOUCH",
    "T/SCLOSE",
    "T/SUNDER",
    "T/SCL",
    "T/SCM",
    "T/SCR",
    "T/SMID",
    "T/SUSMID",
    "T/OSSMID",
    "T/SML",
    "T/SMLC",
    "T/SMC",
    "T/SMRC",
    "T/SMR",
    "T/S3PT",
    "T/SUS3PT",
    "T/OSS3PT",
    "T/S3L",
    "T/S3LC",
    "T/S3C",
    "T/S3RC",
    "T/S3R",
    "T/CONTMID",
    "T/CONT3PT",
    "T/SBMID",
    "T/SB3PT",
    "T/SPINJ",
    "T/TPU3PT",
    "T/DPUMID",
    "T/DPU3PT",
    "T/DRIVE",
    "T/SUDRIVE",
    "T/OSDRIVE",
    "T/GLASS",
    "T/STHRU",
    "T/DRLAYUP",
    "T/SPLAYUP",
    "T/EURO",
    "T/HOPSTEP",
    "T/FLOATER",
    "T/SDUNK",
    "T/DDUNK",
    "T/FDUNK",
    "T/AOOP",
    "T/PUTBACK",
    "T/CRASH",
    "T/DRIVE-R",
    "T/TTPFAKE",
    "T/JABSTEP",
    "T/TTIDLE",
    "T/TTSHOOT",
    "T/SIZEUP",
    "T/HSTTN",
    "T/NOSETUP",
    "T/XOVER",
    "T/2XOVER",
    "T/SPIN",
    "T/HSPIN",
    "T/SBACK",
    "T/BBACK",
    "T/DHSTTN",
    "T/INNOUT",
    "T/NODRIB",
    "T/FINISH",
    "T/DISH",
    "T/FLASHYP",
    "T/A-OOPP",
    "T/ROLLPOP",
    "T/SPOTCUT",
    "T/ISOVSE",
    "T/ISOVSG",
    "T/ISOVSA",
    "T/ISOVSP",
    "T/PLYDISC",
    "T/POSTUP",
    "T/PBDOWN",
    "T/PAGGBD",
    "T/PFACEUP",
    "T/PSPIN",
    "T/PDRIVE",
    "T/PDSTEP",
    "T/PHSTEP",
    "T/PSHOOT",
    "T/PHOOKL",
    "T/PHOOKR",
    "T/PFADEL",
    "T/PFADER",
    "T/PSHIMMY",
    "T/PHSHOT",
    "T/PSBSHOT",
    "T/PUPNUND",
    "T/TAKEC",
    "T/FOUL",
    "T/HFOUL",
    "T/PINTERC",
    "T/STEAL",
    "T/BLOCK",
    "T/CONTEST",
]

# -----------------------------------------------------------------------------
# Attempt to override hard‑coded offsets from a configuration file.
#
# When a unified offsets file is present in the same directory (see
# ``UNIFIED_FILES`` above), it may contain a "Base" object with hex
# addresses used to override the default constants in this module.  This
# allows the tool to adapt to different game versions or user‑supplied
# offset maps without recompiling.  Legacy ``potion.txt`` and
# ``offsets.json`` files are no longer consulted.
import json as _json
import pathlib as _pathlib


# ---- Robust base directory resolver (script or PyInstaller) ----
def _app_base_dir():
    import os, sys, pathlib
    if getattr(sys, 'frozen', False) and hasattr(sys, '_MEIPASS'):
        return pathlib.Path(sys._MEIPASS)
    return pathlib.Path(__file__).resolve().parent
# ----------------------------------------------------------------

# ---------- Robust Offsets path resolver (minimal, non-invasive) ----------
def _find_offsets_path():
    import os, sys
    base = getattr(sys, "_MEIPASS", os.path.dirname(__file__))
    for cand in ("Offsets.txt", "Offsets"):
        path = os.path.join(base, cand)
        if os.path.exists(path):
            return path
    # Last resort: current working dir
    for cand in ("Offsets.txt", "Offsets"):
        if os.path.exists(cand):
            return cand
    raise FileNotFoundError("Offsets file not found (looked for Offsets.txt / Offsets).")
# --------------------------------------------------------------------------

# ---- Resource path helper (works in PyInstaller onefile/onedir and dev) ----
def _resource_path(relative_name: str) -> str:
    import os, sys
    base = getattr(sys, '_MEIPASS', os.path.dirname(__file__))
    return os.path.join(base, relative_name)
# ---------------------------------------------------------------------------
# -----------------------------------------------------------------------------
# Helper to load category definitions from a unified offsets file.
#
# The cheat engine tables describe many fields (Body, Vitals, Attributes,
# Tendencies, Badges, etc.) with bit offsets and lengths.  When building
# a full editor we need to know which fields exist and how to read/write
# their values.  Unified offsets files encode this mapping in JSON format.
# The top‑level keys other than "Base" correspond to categories.  Each entry
# within a category is a dictionary with keys like ``name``, ``offset``,
# ``startBit`` and ``length``.  This helper reads the entire file and
# returns a dict mapping category names to lists of field definitions.
# If no unified file exists or it cannot be parsed, it returns an empty
# dictionary.




def _load_categories() -> dict[str, list[dict]]:
    """
    Load editor categories from Offsets.txt (via offsets_reader) if present.
    Falls back to any unified_offsets*.json file for backward compatibility.
    Returns a dict mapping category name -> list of field dicts
    (each with keys: name, offset, startBit, length[, values]).
    """
    base_dir = _app_base_dir()
    # Prefer Offsets.txt + offsets_reader
    try:
        if offsets_reader is not None:
            for fname in ("Offsets.txt", "Offsets"):
                off_path = base_dir / fname
                if off_path.is_file():
                    raw = offsets_reader.load_offsets(off_path)
                    rs  = offsets_reader.restructure(raw)
                    categories: dict[str, list[dict]] = {}
                    for cat, value in rs.items():
                        if isinstance(value, dict) and cat.lower() != "base":
                            lst: list[dict] = []
                            # Keep deterministic order by offset numeric asc
                            def _to_int(h):
                                try:
                                    return int(h, 16)
                                except Exception:
                                    return 0
                            for off_hex in sorted(value.keys(), key=_to_int):
                                items = value[off_hex]
                                if isinstance(items, dict):
                                    items = [items]
                                if not isinstance(items, list):
                                    continue
                                for field in items:
                                    if not isinstance(field, dict):
                                        continue
                                    fd = dict(field)
                                    fd.setdefault("startBit", 0)
                                    fd["offset"] = off_hex
                                    lst.append(fd)
                            categories[cat] = lst
                    if categories:
                        return categories
    except Exception:
        pass

    # Fallback: try unified offsets JSONs for dev convenience
    for fname in UNIFIED_FILES:
        upath = base_dir / fname
        if not upath.is_file():
            continue
        try:
            with open(upath, "r", encoding="utf-8") as f:
                udata = _json.load(f)
            categories: dict[str, list[dict]] = {}
            if isinstance(udata, dict):
                for key, value in udata.items():
                    if key.lower() == "base":
                        continue
                    if isinstance(value, list) and all(isinstance(x, dict) for x in value):
                        categories[key] = value
            if categories:
                return categories
        except Exception:
            pass
    return {}



def _load_offset_overrides() -> dict[str, str] | None:
    """
    Load the ``Base`` offset definitions from a unified offsets file.

    The returned dictionary contains mappings such as ``"Player Base Address"``
    which override the default constants in this module.
    """
    base_dir = _app_base_dir()

    # Try unified files
    for fname in UNIFIED_FILES:
        upath = base_dir / fname
        if not upath.is_file():
            continue
        try:
            with open(upath, "r", encoding="utf-8") as f:
                udata = _json.load(f)
            if isinstance(udata, dict):
                base = udata.get("Base")
                if isinstance(base, dict):
                    return base
        except Exception:
            continue
    return None


# Apply overrides if present
_offsets = _load_offset_overrides()
if _offsets:
    try:
        PLAYER_TABLE_RVA = int(
            _offsets.get("Player Base Address", hex(PLAYER_TABLE_RVA)), 16
        )
    except Exception:
        pass
    try:
        PLAYER_STRIDE = int(
            _offsets.get("Player Offset Length", hex(PLAYER_STRIDE)), 16
        )
    except Exception:
        pass
    # Name offsets
    try:
        OFF_FIRST_NAME = int(_offsets.get("Offset First Name", hex(OFF_FIRST_NAME)), 16)
    except Exception:
        pass
    try:
        OFF_LAST_NAME = int(_offsets.get("Offset Last Name", hex(OFF_LAST_NAME)), 16)
    except Exception:
        pass
    try:
        OFF_FACE_ID = int(_offsets.get("Offset Face ID", hex(OFF_FACE_ID)), 16)
    except Exception:
        pass
    try:
        OFF_TEAM_PTR = int(_offsets.get("Offset Player Team", hex(OFF_TEAM_PTR)), 16)
    except Exception:
        pass
    try:
        OFF_TEAM_NAME = int(
            _offsets.get("Offset Player Team Name", hex(OFF_TEAM_NAME)), 16
        )
    except Exception:
        pass
    # Adjust name length if provided (convert bytes to UTF‑16 characters)
    try:
        name_bytes = int(_offsets.get("Name Field Length", "0"), 16)
        if name_bytes > 0:
            NAME_MAX_CHARS = max(1, name_bytes // 2)
    except Exception:
        pass

###############################################################################
# Windows API declarations
#
# Only a subset of the Win32 API is required: enumerating processes and
# modules, opening a process, and reading/writing its memory.  These
# declarations mirror those used in the earlier patcher example.  They are
# defined only on Windows; on other platforms the memory access functions
# are unavailable and the tool cannot attach to the game.

if sys.platform == "win32":
    PROCESS_VM_READ = 0x0010
    PROCESS_VM_WRITE = 0x0020
    PROCESS_VM_OPERATION = 0x0008
    PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
    PROCESS_QUERY_INFORMATION = 0x0400
    PROCESS_ALL_ACCESS = (
        PROCESS_VM_READ
        | PROCESS_VM_WRITE
        | PROCESS_VM_OPERATION
        | PROCESS_QUERY_INFORMATION
        | PROCESS_QUERY_LIMITED_INFORMATION
    )

    TH32CS_SNAPPROCESS = 0x00000002
    TH32CS_SNAPMODULE = 0x00000008
    TH32CS_SNAPMODULE32 = 0x00000010

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

    # ---------------------------------------------------------------------
    # Handle potential API changes in ctypes.wintypes
    #
    # In Python 3.13 and later, `ctypes.wintypes` no longer defines
    # `ULONG_PTR`.  We define a compatible `ULONG_PTR` alias based on
    # pointer size so the structures below remain portable across Python
    # versions and architectures.
    try:
        _ULONG_PTR = wintypes.ULONG_PTR
    except AttributeError:
        # Choose 64‑bit or 32‑bit unsigned type depending on pointer size
        _ULONG_PTR = (
            ctypes.c_uint64 if ctypes.sizeof(ctypes.c_void_p) == 8 else ctypes.c_uint32
        )

    class MODULEENTRY32W(ctypes.Structure):
        _fields_ = [
            ("dwSize", wintypes.DWORD),
            ("th32ModuleID", wintypes.DWORD),
            ("th32ProcessID", wintypes.DWORD),
            ("GlblcntUsage", wintypes.DWORD),
            ("ProccntUsage", wintypes.DWORD),
            ("modBaseAddr", wintypes.LPVOID),
            ("modBaseSize", wintypes.DWORD),
            ("hModule", wintypes.HMODULE),
            ("szModule", wintypes.WCHAR * 256),
            ("szExePath", wintypes.WCHAR * 260),
        ]

    class PROCESSENTRY32W(ctypes.Structure):
        _fields_ = [
            ("dwSize", wintypes.DWORD),
            ("cntUsage", wintypes.DWORD),
            ("th32ProcessID", wintypes.DWORD),
            # Use our alias for `ULONG_PTR` to support Python versions where
            # `ctypes.wintypes.ULONG_PTR` is unavailable.
            ("th32DefaultHeapID", _ULONG_PTR),
            ("th32ModuleID", wintypes.DWORD),
            ("cntThreads", wintypes.DWORD),
            ("th32ParentProcessID", wintypes.DWORD),
            ("pcPriClassBase", wintypes.LONG),
            ("dwFlags", wintypes.DWORD),
            ("szExeFile", wintypes.WCHAR * 260),
        ]

    CreateToolhelp32Snapshot = kernel32.CreateToolhelp32Snapshot
    CreateToolhelp32Snapshot.argtypes = [wintypes.DWORD, wintypes.DWORD]
    CreateToolhelp32Snapshot.restype = wintypes.HANDLE

    Module32FirstW = kernel32.Module32FirstW
    Module32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(MODULEENTRY32W)]
    Module32FirstW.restype = wintypes.BOOL

    Module32NextW = kernel32.Module32NextW
    Module32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(MODULEENTRY32W)]
    Module32NextW.restype = wintypes.BOOL

    Process32FirstW = kernel32.Process32FirstW
    Process32FirstW.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
    Process32FirstW.restype = wintypes.BOOL

    Process32NextW = kernel32.Process32NextW
    Process32NextW.argtypes = [wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)]
    Process32NextW.restype = wintypes.BOOL

    OpenProcess = kernel32.OpenProcess
    OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    OpenProcess.restype = wintypes.HANDLE

    CloseHandle = kernel32.CloseHandle
    CloseHandle.argtypes = [wintypes.HANDLE]
    CloseHandle.restype = wintypes.BOOL

    ReadProcessMemory = kernel32.ReadProcessMemory
    ReadProcessMemory.argtypes = [
        wintypes.HANDLE,
        wintypes.LPCVOID,
        wintypes.LPVOID,
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_size_t),
    ]
    ReadProcessMemory.restype = wintypes.BOOL

    WriteProcessMemory = kernel32.WriteProcessMemory
    WriteProcessMemory.argtypes = [
        wintypes.HANDLE,
        wintypes.LPVOID,
        wintypes.LPCVOID,
        ctypes.c_size_t,
        ctypes.POINTER(ctypes.c_size_t),
    ]
    WriteProcessMemory.restype = wintypes.BOOL


class GameMemory:
    """Utility class encapsulating process lookup and memory access."""

    def __init__(self, module_name: str = MODULE_NAME):
        self.module_name = module_name
        self.pid: int | None = None
        self.hproc: wintypes.HANDLE | None = None
        self.base_addr: int | None = None

    # -------------------------------------------------------------------------
    # Process management
    # -------------------------------------------------------------------------
    def find_pid(self) -> int | None:
        """Return the PID of the target process, or None if not found."""
        # Use psutil when available for convenience
        try:
            import psutil  # type: ignore

            for proc in psutil.process_iter(["name"]):
                if (
                    proc.info["name"]
                    and proc.info["name"].lower() == self.module_name.lower()
                ):
                    return proc.pid
        except Exception:
            pass
        # Fallback to toolhelp snapshot on Windows
        if sys.platform != "win32":
            return None
        snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
        if not snap:
            return None
        entry = PROCESSENTRY32W()
        entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
        try:
            success = Process32FirstW(snap, ctypes.byref(entry))
            while success:
                if entry.szExeFile.lower() == self.module_name.lower():
                    return entry.th32ProcessID
                success = Process32NextW(snap, ctypes.byref(entry))
        finally:
            CloseHandle(snap)
        return None

    def open_process(self) -> bool:
        """Open the game process and resolve its base address.

        Returns ``True`` on success and ``False`` on failure.  When the
        process is successfully opened, ``self.pid``, ``self.hproc`` and
        ``self.base_addr`` are set accordingly.
        """
        if sys.platform != "win32":
            # Non‑Windows platforms cannot attach to a process
            self.close()
            return False
        pid = self.find_pid()
        if pid is None:
            self.close()
            return False
        # If already open to the same PID, reuse existing handle
        if self.pid == pid and self.hproc:
            return True
        # Close any existing handle
        self.close()
        # Attempt to open with full access
        handle = OpenProcess(PROCESS_ALL_ACCESS, False, pid)
        if not handle:
            # Could fail due to insufficient privileges
            self.close()
            return False
        # Resolve module base
        base = self._get_module_base(pid, self.module_name)
        if base is None:
            CloseHandle(handle)
            self.close()
            return False
        # Populate fields
        self.pid = pid
        self.hproc = handle
        self.base_addr = base
        return True

    def close(self) -> None:
        """Close any open process handle and reset state."""
        if self.hproc:
            try:
                CloseHandle(self.hproc)
            except Exception:
                pass
        self.pid = None
        self.hproc = None
        self.base_addr = None

    def _get_module_base(self, pid: int, module_name: str) -> int | None:
        """Return the base address of ``module_name`` in the given process."""
        if sys.platform != "win32":
            return None
        # Take a snapshot of modules
        flags = TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32
        snap = CreateToolhelp32Snapshot(flags, pid)
        if not snap:
            return None
        me32 = MODULEENTRY32W()
        me32.dwSize = ctypes.sizeof(MODULEENTRY32W)
        try:
            if not Module32FirstW(snap, ctypes.byref(me32)):
                return None
            while True:
                if me32.szModule.lower() == module_name.lower():
                    return ctypes.cast(me32.modBaseAddr, ctypes.c_void_p).value
                if not Module32NextW(snap, ctypes.byref(me32)):
                    break
        finally:
            CloseHandle(snap)
        return None

    # -------------------------------------------------------------------------
    # Memory access helpers
    # -------------------------------------------------------------------------
    def _check_open(self):
        if self.hproc is None or self.base_addr is None:
            raise RuntimeError("Game process not opened")

    def read_bytes(self, addr: int, length: int) -> bytes:
        """Read ``length`` bytes from absolute address ``addr``."""
        self._check_open()
        buf = (ctypes.c_ubyte * length)()
        read_count = ctypes.c_size_t()
        ok = ReadProcessMemory(
            self.hproc, ctypes.c_void_p(addr), buf, length, ctypes.byref(read_count)
        )
        if not ok or read_count.value != length:
            raise RuntimeError(f"Failed to read memory at 0x{addr:X}")
        return bytes(buf)

    def write_bytes(self, addr: int, data: bytes) -> None:
        """Write ``data`` to absolute address ``addr``."""
        self._check_open()
        length = len(data)
        buf = (ctypes.c_ubyte * length).from_buffer_copy(data)
        written = ctypes.c_size_t()
        ok = WriteProcessMemory(
            self.hproc, ctypes.c_void_p(addr), buf, length, ctypes.byref(written)
        )
        if not ok or written.value != length:
            raise RuntimeError(f"Failed to write memory at 0x{addr:X}")

    def read_uint32(self, addr: int) -> int:
        data = self.read_bytes(addr, 4)
        return struct.unpack("<I", data)[0]

    def write_uint32(self, addr: int, value: int) -> None:
        data = struct.pack("<I", value & 0xFFFFFFFF)
        self.write_bytes(addr, data)

    def read_uint64(self, addr: int) -> int:
        data = self.read_bytes(addr, 8)
        return struct.unpack("<Q", data)[0]

    def read_wstring(self, addr: int, max_chars: int) -> str:
        """Read a UTF‑16LE string of at most ``max_chars`` characters from ``addr``."""
        raw = self.read_bytes(addr, max_chars * 2)
        try:
            s = raw.decode("utf-16le", errors="ignore")
        except Exception:
            return ""
        end = s.find("\x00")
        if end != -1:
            s = s[:end]
        return s

    def write_wstring_fixed(self, addr: int, value: str, max_chars: int) -> None:
        """Write a fixed length null‑terminated UTF‑16LE string at ``addr``."""
        value = value[: max_chars - 1]
        encoded = value.encode("utf-16le") + b"\x00\x00"
        padded = encoded.ljust(max_chars * 2, b"\x00")
        self.write_bytes(addr, padded)
class Player:
    """Container class representing basic player data."""

    def __init__(
        self, index: int, first_name: str, last_name: str, team: str, face_id: int
    ):
        self.index = index
        self.first_name = first_name
        self.last_name = last_name
        self.team = team
        self.face_id = face_id

    @property
    def full_name(self) -> str:
        name = f"{self.first_name} {self.last_name}".strip()
        return name if name else f"Player {self.index}"

    def __repr__(self) -> str:
        return f"<Player index={self.index} name='{self.full_name}' team='{self.team}'>"


class PlayerDataModel:
    """High level API for scanning and editing NBA 2K25 player records."""

    def __init__(self, mem: GameMemory, max_players: int = MAX_PLAYERS):
        self.mem = mem
        self.max_players = max_players
        self.players: list[Player] = []
        # Mapping from normalized full names ("first last") to a list of
        # player indices.  This dictionary is rebuilt each time players are
        # scanned or loaded.  It allows for fast lookup of players by name
        # during imports and other operations.
        self.name_index_map: Dict[str, list[int]] = {}

        # Current list of available teams represented as (index, name) tuples.
        # This will be populated by scanning memory.
        self.team_list: list[tuple[int, str]] = []
        # Mapping of team index to roster type (0 = NBA, 1 = Historic, etc.).
        self.team_types: Dict[int, int] = {}

        # Flag indicating that ``self.players`` was populated by scanning all
        # player records rather than via per‑team scanning.  When true,
        # ``get_players_by_team`` will filter ``self.players`` by team name
        # instead of using roster pointers.
        self.fallback_players: bool = False

        # Internal caches for resolved pointer chains.  During a successful
        # scan, these fields store the computed base address of the player
        # table, the team records and the stadium records.  Subsequent
        # operations use the cached values to avoid repeatedly resolving
        # pointers.  They are reset whenever ``refresh_players`` is called.
        self._resolved_player_base: int | None = None
        self._resolved_team_base: int | None = None

        # List of stadiums discovered in memory.  Each element is
        # (index, arena_name).  Populated via ``_scan_stadium_names``.

        # Load category definitions for advanced editing.  These definitions
        # describe where and how to read/write additional player attributes
        # (e.g. vitals, attributes, tendencies, badges).  They come from
        # unified offsets files if present.  If no unified file is found
        # ``categories`` will be empty and the full editor will display
        # placeholder text.
        try:
            self.categories: dict[str, list[dict]] = _load_categories()
        except Exception:
            self.categories = {}
        # Merge in any extra categories defined by the editor.  If a category
        # already exists, append only new fields.  Otherwise add the
        # category wholesale.  See EXTRA_CATEGORIES for definitions.
        for extra_cat, fields in EXTRA_CATEGORIES.items():
            if extra_cat in self.categories:
                existing = {f.get("name") for f in self.categories[extra_cat]}
                for f in fields:
                    if f.get("name") not in existing:
                        self.categories[extra_cat].append(f)
            else:
                # Use a shallow copy to avoid modifying the global list
                self.categories[extra_cat] = list(fields)
        # Reorder categories based on import header order and extract
        # durability fields into a separate category.  This ensures the
        # editor displays fields in a predictable order matching the
        # provided sample tables and that durability fields are grouped
        # together.  Reordering is done immediately after loading so
        # subsequent operations (e.g. import) use the reordered lists.
        self._reorder_categories()

    # -------------------------------------------------------------------------
    # Category reordering and import helpers
    # -------------------------------------------------------------------------
    def _normalize_header_name(self, name: str) -> str:
        """
        Normalize a column header name for matching against field names.

        This helper performs the following transformations:
        * Converts to uppercase.
        * Removes whitespace and punctuation.
        * Applies header‑specific synonyms (e.g. "LAYUP" becomes
          "DRIVINGLAYUP", "STDUNK" becomes "STANDINGDUNK", etc.).

        Args:
            name: Raw column header from the import file.

        Returns:
            A canonical string used for matching against field names.
        """
        import re as _re

        norm = _re.sub(r"[^A-Za-z0-9]", "", str(name).upper())
        # Apply known header synonyms; map abbreviations to canonical
        # attribute names.  Only a subset of synonyms is defined here; any
        # unknown name will fall back to its normalized form.
        header_synonyms = {
            "LAYUP": "DRIVINGLAYUP",
            "STDUNK": "STANDINGDUNK",
            "DUNK": "DRIVINGDUNK",
            "CLOSE": "CLOSESHOT",
            "MID": "MIDRANGESHOT",
            "3PT": "3PTSHOT",
            "FT": "FREETHROW",
            "PHOOK": "POSTHOOK",
            "PFADE": "POSTFADE",
            "POSTC": "POSTMOVES",
            "FOUL": "DRAWFOUL",
            "BALL": "BALLCONTROL",
            "SPDBALL": "SPEEDWITHBALL",
            "SPDBALL": "SPEEDWITHBALL",
            "PASSIQ": "PASSINGIQ",
            "PASS_IQ": "PASSINGIQ",
            "VISION": "PASSINGVISION",
            "OCNST": "OFFENSIVECONSISTENCY",
            "ID": "INTERIORDEFENSE",
            "PD": "PERIMETERDEFENSE",
            "STEAL": "STEAL",
            "BLOCK": "BLOCK",
            "OREB": "OFFENSIVEREBOUND",
            "DREB": "DEFENSIVEREBOUND",
            "HELPIQ": "HELPDEFENSEIQ",
            "PSPER": "PASSINGPERCEPTION",
            "DCNST": "DEFENSIVECONSISTENCY",
            "SPEED": "SPEED",
            "AGIL": "AGILITY",
            "STR": "STRENGTH",
            "VERT": "VERTICAL",
            "STAM": "STAMINA",
            "INTNGBL": "INTANGIBLES",
            "HSTL": "HUSTLE",
            "DUR": "MISCELLANEOUSDURABILITY",
            "POT": "POTENTIAL",
            # Durability synonyms
            "BACK": "BACKDURABILITY",
            "HEAD": "HEADDURABILITY",
            "LEFTANKLE": "LEFTANKLEDURABILITY",
            "LEFTELBOW": "LEFTELBOWDURABILITY",
            "LEFTFOOT": "LEFTFOOTDURABILITY",
            "LEFTHIP": "LEFTHIPDURABILITY",
            "LEFTKNEE": "LEFTKNEEDURABILITY",
            "LEFTSHOULDER": "LEFTSHOULDERDURABILITY",
            "NECK": "NECKDURABILITY",
            "RIGHTANKLE": "RIGHTANKLEDURABILITY",
            "RIGHTELBOW": "RIGHTELBOWDURABILITY",
            "RIGHTFOOT": "RIGHTFOOTDURABILITY",
            "RIGHTHIP": "RIGHTHIPDURABILITY",
            "RIGHTKNEE": "RIGHTKNEEDURABILITY",
            "RIGHTSHOULDER": "RIGHTSHOULDERDURABILITY",
            "MISCELLANEOUS": "MISCELLANEOUSDURABILITY",
            "MISCELLANEOUSDURABILITY": "MISCELLANEOUSDURABILITY",
            # Tendencies abbreviations (T/ prefixed) mapped to canonical field names.
            # These mappings allow the importer to align columns from the
            # Tendencies spreadsheet with the corresponding field names in
            # the offset map.  Each key is the normalized abbreviation (no
            # punctuation); the value is the normalized field name
            # (uppercase, no spaces) used in the offset map.  This list
            # covers all abbreviations that appear in the user's sheet.
            # Abbreviation mappings for shooting/finishing
            "TSHOT": "SHOOT",  # generic Shot -> Shoot (from user: shot = shoot)
            "TTOUCH": "TOUCHES",
            "TSCLOSE": "SHOTCLOSE",
            "TSUNDER": "SHOTUNDERBASKET",
            "TSCL": "SHOTCLOSELEFT",
            "TSCM": "SHOTCLOSEMIDDLE",
            "TSCR": "SHOTCLOSERIGHT",
            "TSMID": "SHOTMID",
            "TSUSMID": "SPOTUPSHOTMID",
            "TOSSMID": "OFFSCREENSHOTMID",
            "TSML": "SHOTMIDLEFT",
            "TSMLC": "SHOTMIDLEFTCENTER",
            "TSMC": "SHOTMIDCENTER",
            "TSMRC": "SHOTMIDRIGHTCENTER",
            "TSMR": "SHOTMIDRIGHT",
            "TS3PT": "SHOT3PT",
            "TSUS3PT": "SPOTUPSHOT3PT",
            "TOSS3PT": "OFFSCREENSHOT3PT",
            "TS3L": "SHOT3PTLEFT",
            "TS3LC": "SHOT3PTLEFTCENTER",
            "TS3C": "SHOT3PTCENTER",
            "TS3RC": "SHOT3PTRIGHTCENTER",
            "TS3R": "SHOT3PTRIGHT",
            "TCONTMID": "CONTESTEDJUMPERMID",
            "TCONT3PT": "CONTESTEDJUMPER3PT",
            "TSBMID": "STEPBACKJUMPERMID",
            "TSB3PT": "STEPBACKJUMPER3PT",
            # Spin Jumper tendency abbreviation
            "TSPINJ": "SPINJUMPERTENDENCY",
            # Transition pull‑up 3pt (not drive)
            "TTPU3PT": "TRANSITIONPULLUP3PT",
            "TDPUMID": "DRIVEPULLUPMID",
            "TDPU3PT": "DRIVEPULLUP3PT",
            "TDRIVE": "DRIVE",
            "TSUDRIVE": "SPOTUPDRIVE",
            "TOSDRIVE": "OFFSCREENDRIVE",
            # Use Glass tendency; map to USEGLASS rather than Crash
            "TGLASS": "USEGLASS",
            "TSTHRU": "STEPTHROUGHSHOT",
            "TDRLAYUP": "DRIVINGLAYUPTENDENCY",
            "TSPLAYUP": "STANDINGLAYUPTENDENCY",
            "TEURO": "EUROSTEP",
            "THOPSTEP": "HOPSTEP",
            "TFLOATER": "FLOATER",
            "TSDUNK": "STANDINGDUNKTENDENCY",
            "TDDUNK": "DRIVINGDUNKTENDENCY",
            "TFDUNK": "FLASHYDUNKTENDENCY",
            # Alley‑oop dunk tendency
            "TAOOP": "ALLEYOOP",
            "TPUTBACK": "PUTBACK",
            "TCRASH": "CRASH",
            # Drive‑R abbreviation represents Drive Right
            "TDRIVER": "DRIVERIGHT",
            "TTTPFAKE": "TRIPLETHREATPUMPFAKE",
            "TJABSTEP": "TRIPLETHREATJABSTEP",
            "TTTIDLE": "TRIPLETHREATIDLE",
            "TTTSHOOT": "TRIPLETHREATSHOOT",
            # Setup moves (Sizeup and Hesitation) and no setup
            "TSIZEUP": "SETUPWITHSIZEUP",
            "THSTTN": "SETUPWITHHESITATION",
            "TNOSETUP": "NOSETUPDRIBBLE",
            # Dribble move abbreviations map to their driving variants
            "TXOVER": "DRIVINGCROSSOVER",
            "T2XOVER": "DRIVINGDOUBLECROSSOVER",
            # TSPIN abbreviation corresponds to the driving spin dribble move
            "TSPIN": "DRIVINGSPIN",
            # Half spin corresponds to driving half spin
            "THSPIN": "DRIVINGHALFSPIN",
            # Stepback corresponds to driving stepback
            "TSBACK": "DRIVINGSTEPBACK",
            # Behind‑the‑back corresponds to driving behind the back
            "TBBACK": "DRIVINGBEHINDBACK",
            # Double hesitation corresponds to driving dribble hesitation
            "TDHSTTN": "DRIVINGDRIBBLEHESITATION",
            "TINNOUT": "INANDOUT",
            "TNODRIB": "NODRIBBLE",
            "TFINISH": "ATTACKSTRONGONDRIVE",  # finish = attack strong on drive
            "TDISH": "DISHTOOPENMAN",  # dish = dish to open man
            "TFLASHYP": "FLASHYPASS",
            "TAOOPP": "ALLEYOOPPASS",
            # Roll vs Pop ratio (pick and roll) maps to RollVsPop
            "TROLLPOP": "ROLLVSPOP",
            "TSPOTCUT": "SPOTUPCUT",
            "TISOVSE": "ISOVSE",
            "TISOVSG": "ISOVSG",
            "TISOVSA": "ISOVSA",
            "TISOVSP": "ISOVSP",
            "TPLYDISC": "PLAYDISCIPLINE",
            "TPOSTUP": "POSTUP",
            "TPBDOWN": "POSTBACKDOWN",
            "TPAGGBD": "POSTAGGRESSIVEBACKDOWN",
            "TPFACEUP": "POSTFACEUP",
            "TPSPIN": "POSTSPIN",
            "TPDRIVE": "POSTDRIVE",
            "TPDSTEP": "POSTDROPSTEP",
            "TPHSTEP": "POSTHOPSTEP",
            "TPSHOOT": "POSTSHOT",
            "TPHOOKL": "POSTHOOKLEFT",
            "TPHOOKR": "POSTHOOKRIGHT",
            "TPFADEL": "POSTFADELEFT",
            "TPFADER": "POSTFADERIGHT",
            "TPSHIMMY": "POSTSHIMMY",
            "TPHSHOT": "POSTHOPSHOT",
            "TPSBSHOT": "POSTSTEPBACKSHOT",
            "TPUPNUND": "POSTUPANDUNDER",
            "TTAKEC": "TAKECHARGE",
            # General foul tendency
            "TFOUL": "FOUL",
            "THFOUL": "HARDFOUL",
            # Pass Interception tendency
            "TPINTERC": "PASSINTERCEPTION",
            "TSTEAL": "STEAL",
            "TBLOCK": "BLOCK",
            "TCONTEST": "CONTEST",
        }
        # Replace slashes in SPD/BALL etc.
        # Normalize specific patterns
        # Example: SPD/BALL -> SPDBALL, PASS_IQ -> PASSIQ
        if norm in header_synonyms:
            return header_synonyms[norm]
        return norm

    def _normalize_field_name(self, name: str) -> str:
        """
        Normalize a field name from the offset map for matching.

        This helper performs uppercase conversion and removal of
        non‑alphanumeric characters.  No synonyms are applied here since
        the field names are already descriptive.
        """
        import re as _re

        return _re.sub(r"[^A-Za-z0-9]", "", str(name).upper())

    def _reorder_categories(self) -> None:
        """
        Reorder the categories and fields based on predefined import orders
        and group durability fields into their own category.

        This method modifies ``self.categories`` in place.  It does the
        following:

        * Moves any attribute whose name contains ``Durability`` (case
          insensitive) into a new category called ``Durability``.
        * Reorders the ``Attributes`` category according to
          ``ATTR_IMPORT_ORDER`` using normalized names to match.  Any
          fields not listed in the import order remain at the end in
          their original order.
        * Reorders the ``Tendencies`` category according to
          ``TEND_IMPORT_ORDER`` using a fuzzy matching on normalized
          header names and field names.  Unmatched fields remain at the
          end.
        * Reorders the ``Durability`` category according to
          ``DUR_IMPORT_ORDER`` (if the category exists) using normalized
          header names.  Unmatched fields remain at the end.
        """
        # Ensure the categories dict exists
        cats = self.categories or {}
        # ------------------------------------------------------------------
        # Extract durability fields from Attributes
        if "Attributes" in cats:
            attr_fields = cats.get("Attributes", [])
            new_attr = []
            dura_fields = cats.get("Durability", [])  # if already exists
            for fld in attr_fields:
                name = fld.get("name", "")
                norm = self._normalize_field_name(name)
                if "DURABILITY" in norm:
                    dura_fields.append(fld)
                else:
                    new_attr.append(fld)
            cats["Attributes"] = new_attr
            if dura_fields:
                cats["Durability"] = dura_fields

        # ------------------------------------------------------------------
        # Helper to reorder a category based on an import order list
        def reorder(cat_name: str, import_order: list[str]):
            if cat_name not in cats:
                return
            fields = cats[cat_name]
            # Build a list of remaining fields
            remaining = list(fields)
            reordered: list[dict] = []
            for hdr in import_order:
                norm_hdr = self._normalize_header_name(hdr)
                match_idx = -1
                # Find the first field whose normalized name matches or
                # contains the normalized header name.
                for i, f in enumerate(remaining):
                    norm_field = self._normalize_field_name(f.get("name", ""))
                    # Exact or partial match
                    if (
                        norm_hdr == norm_field
                        or norm_hdr in norm_field
                        or norm_field in norm_hdr
                    ):
                        match_idx = i
                        break
                if match_idx >= 0:
                    reordered.append(remaining.pop(match_idx))
            # Append any unmatched fields at the end
            reordered.extend(remaining)
            cats[cat_name] = reordered

        # Reorder attributes, tendencies, durability
        reorder("Attributes", ATTR_IMPORT_ORDER)
        reorder("Tendencies", TEND_IMPORT_ORDER)
        reorder("Durability", DUR_IMPORT_ORDER)
        # Save back in a deterministic order.  We prefer to display
        # categories in a consistent order matching the import tables.
        ordered = {}
        preferred = [
            "Body",
            "Vitals",
            "Attributes",
            "Durability",
            "Tendencies",
            "Badges",
        ]
        for name in preferred:
            if name in cats:
                ordered[name] = cats[name]
        # Append any remaining categories not listed above
        for name, fields in cats.items():
            if name not in ordered:
                ordered[name] = fields
        self.categories = ordered

    def find_player_indices_by_name(self, name: str) -> list[int]:
        """
        Find player indices matching a given full name.

        Args:
            name: Full name as appearing in import files (e.g. "LeBron James").

        Returns:
            A list of integer indices of players whose first and last names
            match the given name (case‑insensitive).  If no match is found
            returns an empty list.
        """
        name = str(name or "").strip()
        if not name:
            return []
        parts = name.split()
        if not parts:
            return []
        first = parts[0].strip()
        last = " ".join(parts[1:]).strip() if len(parts) > 1 else ""
        # Use the name_index_map for efficient lookup if available
        key = f"{first.lower()} {last.lower()}".strip()
        if self.name_index_map:
            return self.name_index_map.get(key, [])
        # Fallback: linear scan over players
        indices: list[int] = []
        for p in self.players:
            if (
                p.first_name.lower() == first.lower()
                and p.last_name.lower() == last.lower()
            ):
                indices.append(p.index)
        return indices

    def import_table(self, category_name: str, filepath: str) -> int:
        """
        Import player data from a tab- or comma-delimited file for a single category.

        The file must have a header row where the first column is the player
        name and the subsequent columns correspond to fields of the given
        category.  The order of columns defines the order in which values
        should be applied.  Column headers are matched to field names using
        normalized strings and simple substring matching.  Values are
        converted to raw bitfield values as required.

        Args:
            category_name: Name of the category to import (e.g. "Attributes",
                "Tendencies", "Durability").
            filepath: Path to the import file.

        Returns:
            The number of players successfully updated.
        """
        import csv as _csv

        # Ensure category exists
        if category_name not in self.categories:
            return 0
        # Open file
        try:
            with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                # Try to detect delimiter: prefer tab, then comma, semicolon
                sample = f.readline()
                delim = "\t" if "\t" in sample else "," if "," in sample else ";"
                # Reset file pointer
                f.seek(0)
                reader = _csv.reader(f, delimiter=delim)
                rows = list(reader)
        except Exception:
            return 0
        if not rows:
            return 0
        header = rows[0]
        if not header or len(header) < 2:
            return 0
        # Build mapping list: for each column after the first, find the field
        # definition in the category.  For Attributes, we use fuzzy name
        # matching; for Tendencies and Durability we rely on column order
        # matching after the fields have been reordered according to the
        # import order lists.  This ensures that abbreviated headers like
        # "T/SCLOSE" map to their corresponding fields (e.g. Shot Close) even
        # without explicit synonyms.
        field_defs = self.categories[category_name]
        mappings: list[dict | None] = []
        # Build normalized field names list once for matching
        norm_fields: list[tuple[str, dict]] = []
        for f in field_defs:
            n = self._normalize_field_name(f.get("name", ""))
            norm_fields.append((n, f))
        # For each column header (skipping player name) attempt to match by name
        for i, col in enumerate(header[1:]):
            n_hdr = self._normalize_header_name(col)
            matched: dict | None = None
            # First attempt fuzzy match: exact or substring in either direction
            for norm_field, f in norm_fields:
                if n_hdr == norm_field or n_hdr in norm_field or norm_field in n_hdr:
                    matched = f
                    break
            if matched is None:
                # Fallback: map by position if within range
                if i < len(field_defs):
                    matched = field_defs[i]
            mappings.append(matched)
        # Process each row
        players_updated = 0
        for row in rows[1:]:
            if not row or len(row) < 2:
                continue
            name = row[0].strip()
            values = row[1:]
            idxs = self.find_player_indices_by_name(name)
            if not idxs:
                continue
            # Apply values to each matching player
            for idx in idxs:
                any_set = False
                for val, meta in zip(values, mappings):
                    if meta is None:
                        continue
                    # Retrieve offset, start_bit and length.  Offsets in
                    # the offset map may be strings (e.g. "0x392"), so
                    # handle hex prefixes gracefully.  If the offset
                    # cannot be parsed, default to zero.
                    off_raw = meta.get("offset", 0)
                    try:
                        if isinstance(off_raw, str):
                            off_str = off_raw.strip()
                            # Allow hex prefixes (0x...) and decimal
                            if off_str.lower().startswith("0x"):
                                offset = int(off_str, 16)
                            else:
                                offset = int(off_str, 0)
                        else:
                            offset = int(off_raw)
                    except Exception:
                        offset = 0
                    start_bit = int(meta.get("startBit", meta.get("start_bit", 0)))
                    length = int(meta.get("length", 0))
                    # Convert string value to integer; ignore non‑numeric
                    try:
                        # Remove percentage signs or other non-digits
                        import re as _re

                        v = _re.sub(r"[^0-9.-]", "", str(val))
                        if not v:
                            continue
                        num = float(v)
                    except Exception:
                        continue
                    # Convert numeric value to raw bits
                    max_raw = (1 << length) - 1
                    if category_name in ("Attributes", "Durability"):
                        # Interpret the imported value directly as a rating on
                        # the 25–99 scale and convert to raw.  Values
                        # outside the expected range are clamped internally.
                        raw = convert_rating_to_raw(num, length)
                    elif category_name == "Tendencies":
                        # Tendencies are 0–100 scale; convert accordingly
                        raw = convert_rating_to_tendency_raw(num, length)
                    else:
                        # Other categories (if any) are assumed to be
                        # percentages ranging 0..100.  Map linearly to the
                        # raw bitfield range.
                        if max_raw > 0:
                            pct = min(max(num, 0.0), 100.0) / 100.0
                            raw = int(round(pct * max_raw))
                        else:
                            raw = 0
                    # Write value
                    if self.set_field_value(idx, offset, start_bit, length, raw):
                        any_set = True
                if any_set:
                    players_updated += 1
        return players_updated

    def import_all(self, file_map: dict[str, str]) -> dict[str, int]:
        """
        Import multiple tables from a mapping of category names to file paths.

        Args:
            file_map: A mapping of category names ("Attributes", "Tendencies",
                "Durability") to file paths.  If a file path is an empty
                string or does not exist, that category will be skipped.

        Returns:
            A dictionary mapping category names to the number of players
            updated for each category.
        """
        results: dict[str, int] = {}
        for cat, path in file_map.items():
            if not path or not os.path.isfile(path):
                results[cat] = 0
                continue
            results[cat] = self.import_table(cat, path)
        return results

    # ---------- NEW: string/label helpers ----------
    @staticmethod
    def _is_printable_ascii(s: str, min_len: int = 2, max_len: int = 48) -> bool:
        """
        Return True if ``s`` is made up of printable characters with a reasonable
        length and contains at least two alphabetic characters.

        Historically this helper enforced a strict 7‑bit ASCII range (32–126),
        which caused perfectly valid team names with curly quotes, dashes or
        accented letters to be rejected.  The scanning logic would then stop
        early after a run of "invalid" entries and miss historic/All‑Time
        teams.  We now use ``str.isprintable()`` to allow any printable
        Unicode character while still ensuring the name isn't empty, isn't
        excessively long, and contains at least two letters (to avoid
        accepting noise like "---" or purely numeric strings).
        """
        if not s:
            return False
        s = s.strip()
        # enforce a minimum and maximum reasonable length
        if not (min_len <= len(s) <= max_len):
            return False
        # all characters must be printable; allow any printable unicode
        if not s.isprintable():
            return False
        # require at least two alphabetic characters
        letters = sum(ch.isalpha() for ch in s)
        return letters >= 2

    @staticmethod
    def _dedupe_team_names(pairs: list[tuple[int, str]]) -> list[tuple[int, str]]:
        """If multiple teams share the same display name, append the index to disambiguate."""
        from collections import Counter, defaultdict

        counts = Counter(name for _, name in pairs)
        seen: defaultdict[str, int] = defaultdict(int)
        out: list[tuple[int, str]] = []
        for idx, name in pairs:
            if counts[name] > 1:
                seen[name] += 1
                out.append((idx, f"{name} [{idx}]"))
            else:
                out.append((idx, name))
        return out

    @staticmethod
    def _format_historic_year(val: int) -> str:
        """Convert a numeric historic year code to a ``'YY-'YY`` string."""
        if val <= 0:
            return ""
        start_year = 1899 + val
        end_year = start_year + 1
        return f"{start_year % 100:02d}-{end_year % 100:02d}"

    def _compose_team_name_from_ptr(self, team_ptr: int) -> str:
        """
        Build a team display name from a raw team pointer by reading the base name
        and, when applicable, appending the historic season (e.g., '96-97').

        Returns "Unknown" if the name isn't printable.
        """
        try:
            base_name = self.mem.read_wstring(team_ptr + OFF_TEAM_NAME, TEAM_NAME_LENGTH).strip()
        except Exception:
            base_name = ""
        # Start with the base name. We will append the year if it exists.
        name = base_name
        # Attempt to read historic year bits from the team structure. Many classic
        # and decade teams encode their season in a dedicated field at
        # ``TEAM_YEAR_OFFSET``. If those bits are non-zero, derive a YY-YY
        # string and append it to the name. Do not rely on the roster type
        # field to decide whether to append the year.
        year_val = 0
        try:
            raw_year = self.mem.read_uint16(team_ptr + TEAM_YEAR_OFFSET)
            year_val = (raw_year >> 3) & 0x7F
        except Exception:
            year_val = 0
        if year_val > 0:
            year_str = self._format_historic_year(year_val)
            if year_str:
                name = f"{name} {year_str}"
        return name if self._is_printable_ascii(name) else "Unknown"

    # ---------------------------------------------------------------------
    # In‑memory team and player scanning
    # ---------------------------------------------------------------------
    def _scan_team_names(self) -> list[tuple[int, str]]:
        """Read team names robustly, skipping noise and keeping historic teams separate.

        This helper uses the pointer chain defined in the Cheat Engine
        "Team Data" table to locate the base of the team records.  It then
        iterates over the first MAX_TEAMS_SCAN records, reading the team name
        string from each record.  Invalid or noisy strings (non-printable ASCII
        or too short) are skipped.  Scanning stops only after a run of
        several invalid entries and some valid teams have been found.
        Duplicate display names are disambiguated by appending the raw team
        index (e.g. "Bulls [87]").

        Returns a list of (team_index, display_name) tuples and caches it on
        ``self.team_list``.
        """
        if not self.mem.hproc or self.mem.base_addr is None:
            return []
        base = self._resolve_team_base_ptr()
        if base is None:
            return []
        results: list[tuple[int, str]] = []
        self.team_types.clear()
        for team_idx in range(MAX_TEAMS_SCAN):
            try:
                raw = self.mem.read_wstring(
                    base + team_idx * TEAM_STRIDE + TEAM_NAME_OFFSET, TEAM_NAME_LENGTH
                ).strip()
            except Exception:
                raw = ""
            name = raw
            # Determine roster type and historic year
            try:
                t_byte = self.mem.read_uint8(
                    base + team_idx * TEAM_STRIDE + TEAM_TYPE_OFFSET
                )
                t_val = (t_byte >> 2) & 0x1F
            except Exception:
                t_val = 0
            # Store roster type for later categorization but don't rely on it
            self.team_types[team_idx] = t_val
            # Attempt to append historic year regardless of roster type. Many
            # classic and decade teams encode their season in the year field.
            year_val = 0
            try:
                year_raw = self.mem.read_uint16(
                    base + team_idx * TEAM_STRIDE + TEAM_YEAR_OFFSET
                )
                year_val = (year_raw >> 3) & 0x7F
            except Exception:
                year_val = 0
            if year_val > 0:
                year_str = self._format_historic_year(year_val)
                if year_str:
                    name = f"{name} {year_str}"
            if self._is_printable_ascii(name):
                results.append((team_idx, name))
        # Disambiguate duplicate names so UI can map the right index
        results = self._dedupe_team_names(results)
        # cache for other features
        self.team_list = results
        return results

    def scan_team_players(self, team_idx: int) -> list[Player]:
        """Retrieve the list of players on a given team.

        This function reads the roster pointers for the specified team and
        returns a list of ``Player`` objects.  It does **not** update
        ``self.players``; instead it always returns a fresh list.

        Args:
            team_idx: Zero‑based team index (0 for 76ers, 1 for Bucks, etc.).

        Returns:
            A list of ``Player`` instances for the specified team, or an
            empty list if reading fails.
        """
        if not self.mem.hproc or self.mem.base_addr is None:
            return []
        # Resolve player and team base pointers using dynamic resolution
        player_table_base = self._resolve_player_table_base()
        if player_table_base is None:
            return []
        team_base_ptr = self._resolve_team_base_ptr()
        if team_base_ptr is None:
            return []
        rec_addr = team_base_ptr + team_idx * TEAM_STRIDE
        players: list[Player] = []
        for slot in range(TEAM_PLAYER_SLOT_COUNT):
            try:
                ptr = self.mem.read_uint64(rec_addr + slot * 8)
            except Exception:
                # Skip this slot if pointer read fails
                continue
            # Skip null pointers
            if not ptr:
                continue
            try:
                # Compute index relative to player table
                idx = int((ptr - player_table_base) // PLAYER_STRIDE)
            except Exception:
                idx = -1
            try:
                last_name = self.mem.read_wstring(
                    ptr + OFF_LAST_NAME, NAME_MAX_CHARS
                ).strip()
                first_name = self.mem.read_wstring(
                    ptr + OFF_FIRST_NAME, NAME_MAX_CHARS
                ).strip()
                face_id = self.mem.read_uint32(ptr + OFF_FACE_ID)
            except Exception:
                # Skip this player if any field cannot be read
                continue
            if not first_name and not last_name:
                continue
            team_name = (
                self.team_list[team_idx][1]
                if (team_idx < len(self.team_list))
                else "Unknown"
            )
            players.append(
                Player(
                    idx if idx >= 0 else len(players),
                    first_name,
                    last_name,
                    team_name,
                    face_id,
                )
            )
        return players

    # -----------------------------------------------------------------
    # Team editing API
    # -----------------------------------------------------------------
    def get_team_fields(self, team_idx: int) -> Dict[str, str] | None:
        """Return the editable fields for the specified team.

        This method reads the team record for the given index and
        extracts each field defined in ``TEAM_FIELDS``.  The return
        value is a mapping from field label to its current string
        value.  If the game process is not open, or the team table
        cannot be resolved, ``None`` is returned.

        Args:
            team_idx: The zero‑based index of the team (0 = 76ers).

        Returns:
            A dictionary mapping field names to their current values,
            or ``None`` if reading fails.
        """
        if not self.mem.hproc or self.mem.base_addr is None:
            return None
        team_base_ptr = self._resolve_team_base_ptr()
        if team_base_ptr is None:
            return None
        rec_addr = team_base_ptr + team_idx * TEAM_RECORD_SIZE
        fields: Dict[str, str] = {}
        for label, (offset, max_chars) in TEAM_FIELDS.items():
            try:
                val = self.mem.read_wstring(rec_addr + offset, max_chars).rstrip("\x00")
            except Exception:
                val = ""
            fields[label] = val
        return fields

    def set_team_fields(self, team_idx: int, values: Dict[str, str]) -> bool:
        """Write the given values into the specified team record.

        Given a mapping of field names to strings, this method writes
        each value back into the corresponding location of the team
        record.  Only fields defined in ``TEAM_FIELDS`` will be
        updated; extra keys in ``values`` are ignored.  Strings are
        truncated to fit within the maximum character length of their
        fields.  The function returns ``True`` if the write succeeds
        for all fields and ``False`` if any errors occur.

        Args:
            team_idx: Zero‑based index of the team.
            values: Mapping from field label to new value.

        Returns:
            ``True`` if all writes succeeded, ``False`` otherwise.
        """
        if not self.mem.hproc or self.mem.base_addr is None:
            return False
        team_base_ptr = self._resolve_team_base_ptr()
        if team_base_ptr is None:
            return False
        rec_addr = team_base_ptr + team_idx * TEAM_RECORD_SIZE
        success = True
        for label, (offset, max_chars) in TEAM_FIELDS.items():
            if label not in values:
                continue
            val = values[label]
            try:
                self.mem.write_wstring_fixed(rec_addr + offset, val, max_chars)
            except Exception:
                success = False
        return success

    def _scan_all_players(self, max_scan: int = 1024) -> list[Player]:
        """Scan sequential player records, labeling unknown/garbage teams as 'Unknown'.

        This method reads up to ``max_scan`` player records from the player table.
        Each record is interpreted using the offsets defined at the top of this file.
        Team names are resolved via the ``OFF_TEAM_PTR`` and ``OFF_TEAM_NAME`` offsets.
        If a team name cannot be read or contains non-printable ASCII, it is labeled
        as "Unknown".  Completely blank records are skipped.  If the scan yields
        mostly non-ASCII names, the result is discarded to avoid false positives.

        Returns a list of ``Player`` instances or an empty list on failure.
        """
        if not self.mem.hproc or self.mem.base_addr is None:
            return []
        table_base = self._resolve_player_table_base()
        if table_base is None:
            return []
        players: list[Player] = []
        for i in range(max_scan):
            p_addr = table_base + i * PLAYER_STRIDE
            try:
                last_name = self.mem.read_wstring(
                    p_addr + OFF_LAST_NAME, NAME_MAX_CHARS
                ).strip()
                first_name = self.mem.read_wstring(
                    p_addr + OFF_FIRST_NAME, NAME_MAX_CHARS
                ).strip()
                face_id = self.mem.read_uint32(p_addr + OFF_FACE_ID)
            except Exception:
                continue
            # Skip blank cards
            if not first_name and not last_name:
                continue
            team_name = "Unknown"
            try:
                team_ptr = self.mem.read_uint64(p_addr + OFF_TEAM_PTR)
                if team_ptr == 0:
                    team_name = "Free Agents"
                else:
                    # Compose a display name that includes the historic year when applicable
                    team_name = self._compose_team_name_from_ptr(team_ptr)
            except Exception:
                pass
            players.append(Player(i, first_name, last_name, team_name, face_id))
        # Basic sanity heuristic: if majority of names are non-ASCII, treat scan as invalid
        if players:
            allowed = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ -'")
            junk = sum(
                1
                for p in players
                if any(ch not in allowed for ch in (p.first_name + p.last_name))
            )
            if junk > len(players) * 0.5:
                return []
        return players

    def refresh_players(self) -> None:
        """Populate team and player information."""
        # Reset state
        self.team_list = []
        self.players = []
        self.fallback_players = False
        self._resolved_player_base = None
        self._resolved_team_base = None
        

        if self.mem.open_process():
            team_base = self._resolve_team_base_ptr()
            if team_base is not None:
                teams = self._scan_team_names()
                if teams:
                    # Sort teams, grouping those starting with 'Team ' last
                    def _key(item: tuple[int, str]) -> tuple[int, str]:
                        idx, name = item
                        return (
                            1 if name.strip().lower().startswith("team ") else 0,
                            name,
                        )

                    self.team_list = sorted(teams, key=_key)
                    return
            # Fallback: scan players and derive team names from their team pointers
            players = self._scan_all_players(self.max_players)
            if players:
                # Attempt to disambiguate teams by their pointer when multiple
                # historic teams share the same display name.  When scanning
                # fails to resolve the team table, we still know the base of
                # the player table.  Use it to re-read each player's team
                # pointer and build a mapping from pointer -> display name.  If
                # the year field can be read from the team record, include it
                # in the display name; otherwise append a suffix to
                # disambiguate duplicates.
                ptr_to_name: Dict[int, str] = {}
                name_to_ptrs: Dict[str, list[int]] = {}
                table_base = self._resolve_player_table_base()
                if table_base is not None:
                    for p in players:
                        p_addr = table_base + p.index * PLAYER_STRIDE
                        try:
                            ptr = self.mem.read_uint64(p_addr + OFF_TEAM_PTR)
                        except Exception:
                            ptr = 0
                        # Compose a display name directly from the pointer.
                        # This uses the unified offsets (TEAM_NAME_OFFSET and
                        # TEAM_YEAR_OFFSET) to append a historic season when
                        # available.  It will fall back to the base name or
                        # "Unknown" if anything fails.
                        name = self._compose_team_name_from_ptr(ptr) if ptr else "Free Agents"
                        ptr_to_name[ptr] = name
                        name_to_ptrs.setdefault(name, []).append(ptr)
                    # For names that map to multiple pointers (i.e. still
                    # identical after attempting to include the year), append
                    # an index to disambiguate them.  This ensures that
                    # classic teams with identical names remain separate.  The
                    # ordering of indices is deterministic to maintain stable
                    # names between scans.
                    for name, ptrs in name_to_ptrs.items():
                        if len(ptrs) > 1:
                            seen: set[int] = set()
                            unique_ptrs: list[int] = []
                            for ptr in ptrs:
                                if ptr not in seen:
                                    seen.add(ptr)
                                    unique_ptrs.append(ptr)
                            for suffix_idx, ptr in enumerate(unique_ptrs):
                                ptr_to_name[ptr] = f"{name} [{suffix_idx}]"
                    # Update each player's team label based on the pointer
                    for p in players:
                        p_addr = table_base + p.index * PLAYER_STRIDE
                        try:
                            ptr = self.mem.read_uint64(p_addr + OFF_TEAM_PTR)
                        except Exception:
                            ptr = 0
                        if ptr in ptr_to_name:
                            p.team = ptr_to_name[ptr]
                    unique_names = sorted(set(ptr_to_name.values()))
                else:
                    # Could not resolve player table again; fall back to name set
                    unique_names = sorted({p.team for p in players})
                # Apply the 'Team ' sorting heuristic
                def _k(name: str) -> tuple[int, str]:
                    return (1 if name.strip().lower().startswith("team ") else 0, name)
                ordered_names = sorted(unique_names, key=_k)
                # Convert to (index, name) pairs and disambiguate if needed
                pairs = [(i, n) for i, n in enumerate(ordered_names)]
                pairs = self._dedupe_team_names(pairs)
                self.team_list = pairs
                self.players = players
                self.fallback_players = True
                self._build_name_index_map()
                return
        # If nothing was found, lists remain empty
        return

    # ---------------------------------------------------------------------
    # Name index map
    # ---------------------------------------------------------------------
    def _build_name_index_map(self) -> None:
        """
        Rebuild the internal mapping of normalized full names to player indices.

        This method should be invoked whenever ``self.players`` is assigned a new
        list (e.g. after scanning).  It constructs a
        dictionary mapping each player's lower‑cased "first last" name to a
        list of indices.  Using this mapping allows for O(1) lookups of
        players by name instead of scanning the entire ``self.players`` list.
        """
        self.name_index_map.clear()
        for p in self.players:
            first = p.first_name.strip().lower()
            last = p.last_name.strip().lower()
            if not first and not last:
                continue
            key = f"{first} {last}".strip()
            self.name_index_map.setdefault(key, []).append(p.index)

    # -----------------------------------------------------------------
    # Low‑level field access for advanced editing
    # -----------------------------------------------------------------
    def get_field_value(
        self, player_index: int, offset: int, start_bit: int, length: int
    ) -> int | None:
        """
        Retrieve the numeric value of a bit field from a player's record.

        Parameters
        ----------
        player_index : int
            Index of the player within the player table.
        offset : int
            Byte offset within the player record where the bit field begins.
        start_bit : int
            Bit offset (0–7) within the first byte at ``offset``.
        length : int
            Number of bits in the bit field.

        Returns
        -------
        int | None
            The value of the bit field, or ``None`` if it cannot be read.
        """
        try:
            # Ensure process is open
            if not self.mem.open_process():
                return None
            base = self._resolve_player_table_base()
            if base is None:
                return None
            # Calculate address of the field
            addr = base + player_index * PLAYER_STRIDE + offset
            # Determine number of bytes needed
            bits_needed = start_bit + length
            bytes_needed = (bits_needed + 7) // 8
            raw = self.mem.read_bytes(addr, bytes_needed)
            val = int.from_bytes(raw, "little")
            val >>= start_bit
            mask = (1 << length) - 1
            return val & mask
        except Exception:
            return None

    def set_field_value(
        self, player_index: int, offset: int, start_bit: int, length: int, value: int
    ) -> bool:
        """
        Write a numeric value into a player's bit field.

        Parameters
        ----------
        player_index : int
            Index of the player within the player table.
        offset : int
            Byte offset within the player record where the bit field begins.
        start_bit : int
            Bit offset within the first byte at ``offset``.
        length : int
            Number of bits in the bit field.
        value : int
            New value to write.  Values outside the valid range will be
            clamped to the nearest valid value.

        Returns
        -------
        bool
            True on success, False on failure.
        """
        try:
            if not self.mem.open_process():
                return False
            base = self._resolve_player_table_base()
            if base is None:
                return False
            # Clamp value to valid range
            max_val = (1 << length) - 1
            value = max(0, min(max_val, int(value)))
            addr = base + player_index * PLAYER_STRIDE + offset
            bits_needed = start_bit + length
            bytes_needed = (bits_needed + 7) // 8
            data = bytearray(self.mem.read_bytes(addr, bytes_needed))
            current = int.from_bytes(data, "little")
            mask = ((1 << length) - 1) << start_bit
            current &= ~mask
            current |= (value << start_bit) & mask
            new_bytes = current.to_bytes(bytes_needed, "little")
            self.mem.write_bytes(addr, new_bytes)
            return True
        except Exception:
            return False

    # -----------------------------------------------------------------
    # Pointer resolution helpers
    # -----------------------------------------------------------------
    def _resolve_player_table_base(self) -> int | None:
        """Resolve and cache the base pointer of the player table.

        The player records in NBA 2K25 are laid out as a contiguous
        array of fixed‑size structures.  Different game patches use
        slightly different pointer chains to locate this array.  This
        method iterates over a list of candidate chains defined in
        ``PLAYER_PTR_CHAINS``.  Each chain is a tuple
        ``(rva_offset, final_offset, extra_deref)`` where:

        * ``rva_offset`` is added to the module base to obtain an
          initial pointer address.  The 64‑bit value stored at this
          address is read.
        * If ``extra_deref`` is true, the value read from the first
          address is dereferenced again (i.e. another 64‑bit read is
          performed with no added offset).  Some patches embed the
          pointer to the table one level deeper, so this extra
          dereference is needed.
        * ``final_offset`` is added to the result of the pointer
          dereferencing.  The sum is assumed to be the address of the
          first player record.

        For each candidate, a basic sanity check is performed by
        reading the first player's name fields.  If at least one
        chain succeeds, the resolved address is cached and returned.
        If all chains fail, the method falls back to the static RVA
        ``PLAYER_TABLE_RVA``.  Returns ``None`` if no plausible
        address is found.
        """
        # Return cached result if present
        if self._resolved_player_base is not None:
            return self._resolved_player_base
        if not self.mem.hproc or self.mem.base_addr is None:
            return None
        for rva_off, final_off, extra_deref in PLAYER_PTR_CHAINS:
            try:
                p0_addr = self.mem.base_addr + rva_off
                p = self.mem.read_uint64(p0_addr)
                # Some patches require an extra dereference here.  For
                # example, ``[[base+rva]]`` rather than just
                # ``[base+rva]``.  Only perform this when requested.
                if extra_deref:
                    p = self.mem.read_uint64(p)
                # Apply the final offset to arrive at the table base
                table_base = p + final_off
                # Sanity check: read the first player's names
                ln = self.mem.read_wstring(
                    table_base + OFF_LAST_NAME, NAME_MAX_CHARS
                ).strip()
                fn = self.mem.read_wstring(
                    table_base + OFF_FIRST_NAME, NAME_MAX_CHARS
                ).strip()
                if ln or fn:
                    self._resolved_player_base = table_base
                    return table_base
            except Exception:
                continue
        # Fallback: use static RVA if defined
        try:
            fallback_addr = self.mem.base_addr + PLAYER_TABLE_RVA
            ln = self.mem.read_wstring(
                fallback_addr + OFF_LAST_NAME, NAME_MAX_CHARS
            ).strip()
            fn = self.mem.read_wstring(
                fallback_addr + OFF_FIRST_NAME, NAME_MAX_CHARS
            ).strip()
            if ln or fn:
                self._resolved_player_base = fallback_addr
                return fallback_addr
        except Exception:
            pass
        return None

    def _resolve_team_base_ptr(self) -> int | None:
        """Resolve and cache the base pointer of the team records.

        Like the player table, the team records are located via a
        pointer chain that varies between game patches.  Each entry in
        ``TEAM_PTR_CHAINS`` is a tuple ``(rva_offset, final_offset,
        extra_deref)`` analogous to the player pointer chains.  The
        resolution proceeds as follows for each candidate:

        1. Compute ``p0_addr = module_base + rva_offset``.
        2. Read a 64‑bit pointer ``p = [p0_addr]``.
        3. If ``extra_deref`` is true, read another pointer from ``p``
           (i.e. ``p = [p]``).  Otherwise use ``p`` as is.
        4. Add ``final_offset`` to ``p`` to obtain the address of
           the first team record (team index 0).
        5. Read the team name at ``team_base + TEAM_NAME_OFFSET`` and
           check that it contains printable characters.

        The first chain that yields a plausible team name is cached
        and returned.  If no chains produce a valid name, ``None``
        is returned.
        """
        if self._resolved_team_base is not None:
            return self._resolved_team_base
        if not self.mem.hproc or self.mem.base_addr is None:
            return None
        for rva_off, final_off, extra_deref in TEAM_PTR_CHAINS:
            try:
                p0_addr = self.mem.base_addr + rva_off
                p = self.mem.read_uint64(p0_addr)
                if extra_deref:
                    p = self.mem.read_uint64(p)
                team_base = p + final_off
                # Validate by reading the first team name.  Historically
                # validation required every character to be 7‑bit ASCII, which
                # caused patches with curly quotes, dashes or accented
                # characters to fail.  Instead, require the string to be
                # printable and contain at least two letters.
                name = self.mem.read_wstring(
                    team_base + TEAM_NAME_OFFSET, TEAM_NAME_LENGTH
                ).strip()
                if name:
                    # if the string is printable and has two letters, accept
                    if name.isprintable() and sum(ch.isalpha() for ch in name) >= 2:
                        self._resolved_team_base = team_base
                        return team_base
            except Exception:
                continue
        return None

    def get_teams(self) -> list[str]:
        """Return the list of team names in a logical order.

        This method returns a list of team names that has been
        categorised and reordered to improve usability.  When team
        information has been scanned from memory, the underlying
        ``team_list`` remains in its original order (to preserve
        pointer indices), but the returned list groups teams as
        follows:

          1. Free agency / Free Agents entries
          2. Draft Class (if present)
          3. Standard NBA teams
          4. Historic teams (roster type 1 or 24)
          5. All‑Time teams (roster type 25 or names containing "All Time" or "All‑Time")
          6. G‑League teams (names containing "G League", "G-League" or "GLeague")

        Within each category the original order is preserved.
        """
        if self.team_list:
            free: list[str] = []
            draft: list[str] = []
            base: list[str] = []
            historic: list[str] = []
            all_time: list[str] = []
            g_league: list[str] = []
            for idx, name in self.team_list:
                ln = name.lower()
                t = self.team_types.get(idx, 0)
                if "free" in ln:
                    free.append(name)
                elif "draft" in ln:
                    draft.append(name)
                elif t in (1, 24):
                    historic.append(name)
                elif t == 25 or "all time" in ln or "all-time" in ln:
                    all_time.append(name)
                elif "gleague" in ln or "g league" in ln or "g-league" in ln:
                    g_league.append(name)
                else:
                    base.append(name)
            return free + draft + base + historic + all_time + g_league
        # Offline fallback: derive categories from player team names
        names_set = {p.team for p in self.players}
        names = list(names_set)
        lower_names = [n.lower() for n in names]
        free = [names[i] for i, ln in enumerate(lower_names) if "free" in ln]
        draft = [names[i] for i, ln in enumerate(lower_names) if "draft" in ln]
        all_time = [
            names[i]
            for i, ln in enumerate(lower_names)
            if "all time" in ln or "all-time" in ln
        ]
        g_league = [
            names[i]
            for i, ln in enumerate(lower_names)
            if "gleague" in ln or "g league" in ln or "g-league" in ln
        ]
        assigned = set(free + draft + all_time + g_league)
        base = [n for n in names if n not in assigned]
        return free + draft + base + all_time + g_league

    def get_players_by_team(self, team: str) -> list[Player]:
        """Return players for the specified team.

        If team data has been scanned from memory, use the team index
        mapping to look up players dynamically.  Otherwise, filter
        preloaded players (fallback mode).
        """
        if self.team_list:
            if self.fallback_players:
                return [p for p in self.players if p.team == team]
            for idx, name in self.team_list:
                if name == team:
                    return self.scan_team_players(idx)
            return []
        return [p for p in self.players if p.team == team]

    def update_player(self, player: Player) -> None:
        """Write changes to a player back to memory if connected."""
        if not self.mem.hproc or self.mem.base_addr is None:
            return
        # Resolve dynamic player table base pointer
        table_base = self._resolve_player_table_base()
        if table_base is None:
            return
        p_addr = table_base + player.index * PLAYER_STRIDE
        # Write names (fixed length strings)
        self.mem.write_wstring_fixed(
            p_addr + OFF_LAST_NAME, player.last_name, NAME_MAX_CHARS
        )
        self.mem.write_wstring_fixed(
            p_addr + OFF_FIRST_NAME, player.first_name, NAME_MAX_CHARS
        )
        # Write face ID
        self.mem.write_uint32(p_addr + OFF_FACE_ID, player.face_id)

    # ---------------------------------------------------------------------
    # Bulk copy operations
    # ---------------------------------------------------------------------
    def copy_player_data(
        self, src_index: int, dst_index: int, categories: list[str]
    ) -> bool:
        """Copy blocks of data from one player to another.

        This function copies selected portions of the player record from
        ``src_index`` to ``dst_index``.  Valid category names are
        ``"appearance"``, ``"attributes"``, ``"tendencies"``, ``"badges"`` and
        ``"full"``.  Returns ``True`` on success or ``False`` if an error
        occurs (for example, if the process is not open or indices are out
        of bounds).
        """
        if not self.mem.hproc or self.mem.base_addr is None:
            return False
        # Resolve dynamic player table base pointer
        table_base = self._resolve_player_table_base()
        if table_base is None:
            return False
        # Validate indices
        if (
            src_index < 0
            or dst_index < 0
            or src_index >= len(self.players)
            or dst_index >= len(self.players)
        ):
            return False
        src_addr = table_base + src_index * PLAYER_STRIDE
        dst_addr = table_base + dst_index * PLAYER_STRIDE
        try:
            for cat in categories:
                c = cat.lower()
                if c == "appearance":
                    data = self.mem.read_bytes(
                        src_addr + OFF_APPEARANCE, LEN_APPEARANCE
                    )
                    self.mem.write_bytes(dst_addr + OFF_APPEARANCE, data)
                elif c == "attributes":
                    data = self.mem.read_bytes(
                        src_addr + OFF_ATTRIBUTES, LEN_ATTRIBUTES
                    )
                    self.mem.write_bytes(dst_addr + OFF_ATTRIBUTES, data)
                elif c == "tendencies":
                    data = self.mem.read_bytes(
                        src_addr + OFF_TENDENCIES, LEN_TENDENCIES
                    )
                    self.mem.write_bytes(dst_addr + OFF_TENDENCIES, data)
                elif c == "badges":
                    data = self.mem.read_bytes(src_addr + OFF_BADGES, LEN_BADGES)
                    self.mem.write_bytes(dst_addr + OFF_BADGES, data)
                elif c == "full":
                    # Copy entire player record
                    data = self.mem.read_bytes(src_addr, PLAYER_STRIDE)
                    self.mem.write_bytes(dst_addr, data)
            return True
        except Exception:
            return False


class PlayerEditorApp(tk.Tk):
    """The main Tkinter application for editing player data."""

    def __init__(self, model: PlayerDataModel):
        super().__init__()
        self.model = model
        self.title("2K25 Offline Player Data Editor")
        self.geometry("1000x600")
        self.minsize(800, 500)

        # State variables
        self.selected_player: Player | None = None
        self.scanning = False
        # Maintain a list of players for the currently selected team.  This
        # list is filtered by the search bar on the players screen.
        # ``current_players`` holds the Player objects for the selected team,
        # while ``filtered_player_indices`` maps the visible listbox rows
        # back to the indices within ``current_players``.  ``player_search_var``
        # tracks the current search text.
        self.current_players: list[Player] = []
        self.filtered_player_indices: list[int] = []
        self.player_search_var = tk.StringVar()

        # Build UI elements
        self._build_sidebar()
        self._build_home_screen()
        self._build_players_screen()
        self._build_teams_screen()
        # Show home by default
        self.show_home()

    # ---------------------------------------------------------------------
    # Sidebar and navigation
    # ---------------------------------------------------------------------
    def _build_sidebar(self):
        self.sidebar = tk.Frame(self, width=200, bg="#2F3E46")
        self.sidebar.pack(side=tk.LEFT, fill=tk.Y)
        self.sidebar.pack_propagate(False)
        # Buttons
        self.btn_home = tk.Button(
            self.sidebar,
            text="Home",
            command=self.show_home,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_home.pack(fill=tk.X, padx=10, pady=(20, 5))
        self.btn_players = tk.Button(
            self.sidebar,
            text="Players",
            command=self.show_players,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_players.pack(fill=tk.X, padx=10, pady=5)

        # Teams button
        self.btn_teams = tk.Button(
            self.sidebar,
            text="Teams",
            command=self.show_teams,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_teams.pack(fill=tk.X, padx=10, pady=5)

        # Randomizer button
        self.btn_randomizer = tk.Button(
            self.sidebar,
            text="Randomize",
            command=self._open_randomizer,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_randomizer.pack(fill=tk.X, padx=10, pady=5)

        # 2K COY button
        # This button imports player data from external tables (e.g. Google
        # Sheets export) and applies it to the roster.  It expects the
        # import files to follow the same column ordering as the batch
        # import functionality already implemented.  When complete it
        # displays a summary of how many players were updated and
        # lists any players that could not be found.  See
        # ``_open_2kcoy`` for details.
        self.btn_coy = tk.Button(
            self.sidebar,
            text="2K COY",
            command=self._open_2kcoy,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_coy.pack(fill=tk.X, padx=10, pady=5)

        # Load Excel button
        # This button imports player data from a user‑selected Excel workbook.
        # It prompts the user to choose the workbook first, then asks which
        # categories (Attributes, Tendencies, Durability) should be applied.  A
        # loading dialog is displayed while processing to discourage
        # interaction.  See ``_open_load_excel`` for details.
        self.btn_load_excel = tk.Button(
            self.sidebar,
            text="Load Excel",
            command=self._open_load_excel,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_load_excel.pack(fill=tk.X, padx=10, pady=5)

        # Team Shuffle button
        self.btn_shuffle = tk.Button(
            self.sidebar,
            text="Shuffle Teams",
            command=self._open_team_shuffle,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_shuffle.pack(fill=tk.X, padx=10, pady=5)

        # Batch Edit button
        self.btn_batch_edit = tk.Button(
            self.sidebar,
            text="Batch Edit",
            command=self._open_batch_edit,
            bg="#354F52",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        )
        self.btn_batch_edit.pack(fill=tk.X, padx=10, pady=5)

    # ---------------------------------------------------------------------
    # Home screen
    # ---------------------------------------------------------------------
    def _build_home_screen(self):
        self.home_frame = tk.Frame(self, bg="#CAD2C5")
        # Title
        
        
        # Load and display the homepage logo (safe if PIL missing)
        try:
            try:
                from PIL import Image, ImageTk  # type: ignore
            except Exception:
                Image = None
                ImageTk = None

            import os
            logo_candidates = [
                _resource_path("homepage_logo.png"),
                os.path.join(os.getcwd(), "homepage_logo.png")
            ]

            logo_path = next((p for p in logo_candidates if os.path.isfile(p)), None)
            if logo_path and Image and ImageTk:
                img = Image.open(logo_path)
                img = img.resize((250, 250), getattr(Image, "LANCZOS", 1))
                self.logo_img = ImageTk.PhotoImage(img)
                tk.Label(self.home_frame, image=self.logo_img, bg="#CAD2C5").pack(pady=(20, 10))
        except Exception as e:
            print("Logo load failed:", e)

        tk.Label(
            self.home_frame,
            text="2K25 Offline Player Editor",
            font=("Segoe UI", 20, "bold"),
            bg="#CAD2C5",
            fg="#2F3E46",
        ).pack(pady=(40, 20))
        # Status
        self.status_var = tk.StringVar()
        self.status_label = tk.Label(
            self.home_frame,
            textvariable=self.status_var,
            font=("Segoe UI", 12),
            bg="#CAD2C5",
            fg="#2F3E46",
        )
        self.status_label.pack(pady=10)
        # Refresh button
        tk.Button(
            self.home_frame,
            text="Refresh",
            command=self._update_status,
            bg="#84A98C",
            fg="white",
            relief=tk.FLAT,
            activebackground="#52796F",
            activeforeground="white",
        ).pack(pady=5)
        # Version label
        tk.Label(
            self.home_frame,
            text=f"Version {APP_VERSION}",
            font=("Segoe UI", 9, "italic"),
            bg="#CAD2C5",
            fg="#52796F",
        ).pack(side=tk.BOTTOM, pady=10)

    # ---------------------------------------------------------------------
    # Players screen
    # ---------------------------------------------------------------------
    def _build_players_screen(self):
        self.players_frame = tk.Frame(self, bg="#F5F5F5")
        # Top bar for team selection
        top = tk.Frame(self.players_frame, bg="#F5F5F5")
        top.pack(side=tk.TOP, fill=tk.X, pady=10, padx=10)
        tk.Label(
            top, text="Team:", font=("Segoe UI", 12), bg="#F5F5F5", fg="#2F3E46"
        ).pack(side=tk.LEFT)
        self.team_var = tk.StringVar()
        self.team_dropdown = ttk.Combobox(
            top, textvariable=self.team_var, state="readonly"
        )
        self.team_dropdown.bind("<<ComboboxSelected>>", self._on_team_selected)
        self.team_dropdown.pack(side=tk.LEFT, padx=5)
        # Search entry to filter players in the list.  Typing in this box will
        # update ``filtered_player_indices`` and repopulate the listbox.  The
        # default text uses a grey placeholder which disappears on focus.
        search_frame = tk.Frame(top, bg="#F5F5F5")
        search_frame.pack(side=tk.LEFT, padx=10)
        self.search_entry = tk.Entry(
            search_frame, textvariable=self.player_search_var, width=20
        )
        self.search_entry.pack(side=tk.LEFT)
        self.search_entry.insert(0, "Search players…")
        self.search_entry.configure(fg="#8E8E8E")

        # When the entry gains focus, clear the placeholder.  When focus is lost
        # and the entry is empty, restore the placeholder.
        def _on_search_focus_in(_event):
            if self.search_entry.get() == "Search players…":
                self.search_entry.delete(0, tk.END)
                self.search_entry.configure(fg="#2F3E46")

        def _on_search_focus_out(_event):
            if not self.search_entry.get():
                self.search_entry.insert(0, "Search players…")
                self.search_entry.configure(fg="#8E8E8E")

        self.search_entry.bind("<FocusIn>", _on_search_focus_in)
        self.search_entry.bind("<FocusOut>", _on_search_focus_out)
        # When text is entered, filter the player list
        self.player_search_var.trace_add(
            "write", lambda *args: self._filter_player_list()
        )
        self.scan_status_label = tk.Label(
            top, text="", font=("Segoe UI", 10, "italic"), bg="#F5F5F5", fg="#52796F"
        )
        self.scan_status_label.pack(side=tk.LEFT, padx=10)
        # Middle area divided into list and detail
        mid = tk.Frame(self.players_frame, bg="#F5F5F5")
        mid.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        # Player list
        left_pane = tk.Frame(mid, bg="#F5F5F5")
        left_pane.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 10))
        self.player_listbox = tk.Listbox(
            left_pane,
            selectmode=tk.SINGLE,
            exportselection=False,
            font=("Segoe UI", 11),
        )
        self.player_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.player_listbox.bind("<<ListboxSelect>>", self._on_player_selected)
        # Double‑click a player to open the full editor immediately.  This
        # allows editing without having to click the "Open Editor" button.
        self.player_listbox.bind(
            "<Double-Button-1>", lambda e: self._open_full_editor()
        )
        scrollbar = tk.Scrollbar(
            left_pane, orient=tk.VERTICAL, command=self.player_listbox.yview
        )
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.player_listbox.config(yscrollcommand=scrollbar.set)
        # Detail pane
        detail = tk.Frame(mid, bg="#FFFFFF", relief=tk.RIDGE, bd=1)
        detail.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        tk.Label(
            detail,
            text="Player Details",
            font=("Segoe UI", 14, "bold"),
            bg="#FFFFFF",
            fg="#2F3E46",
        ).pack(pady=(5, 10))
        # Name fields
        form = tk.Frame(detail, bg="#FFFFFF")
        form.pack(fill=tk.X, pady=5, padx=10)
        tk.Label(form, text="First Name:", bg="#FFFFFF").grid(
            row=0, column=0, sticky=tk.W
        )
        self.var_first = tk.StringVar()
        self.entry_first = tk.Entry(form, textvariable=self.var_first)
        self.entry_first.grid(row=0, column=1, sticky=tk.EW, padx=5)
        tk.Label(form, text="Last Name:", bg="#FFFFFF").grid(
            row=1, column=0, sticky=tk.W
        )
        self.var_last = tk.StringVar()
        self.entry_last = tk.Entry(form, textvariable=self.var_last)
        self.entry_last.grid(row=1, column=1, sticky=tk.EW, padx=5)
        form.columnconfigure(1, weight=1)
        # Face ID field
        form2 = tk.Frame(detail, bg="#FFFFFF")
        form2.pack(fill=tk.X, pady=5, padx=10)
        tk.Label(form2, text="Face ID:", bg="#FFFFFF").grid(
            row=0, column=0, sticky=tk.W
        )
        self.var_face = tk.StringVar()
        self.entry_face = tk.Entry(form2, textvariable=self.var_face)
        self.entry_face.grid(row=0, column=1, sticky=tk.EW, padx=5)
        form2.columnconfigure(1, weight=1)
        # Team label
        form3 = tk.Frame(detail, bg="#FFFFFF")
        form3.pack(fill=tk.X, pady=5, padx=10)
        tk.Label(form3, text="Team:", bg="#FFFFFF").grid(row=0, column=0, sticky=tk.W)
        self.var_player_team = tk.StringVar()
        tk.Label(
            form3, textvariable=self.var_player_team, bg="#FFFFFF", fg="#2F3E46"
        ).grid(row=0, column=1, sticky=tk.W, padx=5)
        # Buttons
        button_frame = tk.Frame(detail, bg="#FFFFFF")
        button_frame.pack(fill=tk.X, pady=10, padx=10)
        self.btn_save = tk.Button(
            button_frame,
            text="Save",
            command=self._save_player,
            bg="#84A98C",
            fg="white",
            relief=tk.FLAT,
            state=tk.DISABLED,
        )
        self.btn_save.pack(side=tk.LEFT, padx=5)
        self.btn_edit = tk.Button(
            button_frame,
            text="Open Editor",
            command=self._open_full_editor,
            bg="#52796F",
            fg="white",
            relief=tk.FLAT,
            state=tk.DISABLED,
        )
        self.btn_edit.pack(side=tk.LEFT, padx=5)

        # Copy button: opens a dialog to copy data from the selected player to another
        self.btn_copy = tk.Button(
            button_frame,
            text="Copy...",
            command=self._open_copy_dialog,
            bg="#52796F",
            fg="white",
            relief=tk.FLAT,
            state=tk.DISABLED,
        )
        self.btn_copy.pack(side=tk.LEFT, padx=5)

        # Import button: opens a dialog to import player tables (Attributes, Tendencies, Durability)
        self.btn_import = tk.Button(
            button_frame,
            text="Import Data",
            command=self._open_import_dialog,
            bg="#52796F",
            fg="white",
            relief=tk.FLAT,
        )
        self.btn_import.pack(side=tk.LEFT, padx=5)

    # ---------------------------------------------------------------------
    # Navigation methods
    # ---------------------------------------------------------------------
    def show_home(self):
        """
        Display the Home screen and hide any other visible panes."""
        try:
            self.players_frame.pack_forget()
        except Exception:
            pass
        try:
            self.teams_frame.pack_forget()
        except Exception:
            pass
        # Show the home screen
        self.home_frame.pack(fill=tk.BOTH, expand=True)
        self._update_status()

    def show_players(self):
        """
        Display the Players screen and hide other panes."""
        try:
            self.home_frame.pack_forget()
        except Exception:
            pass
        try:
            self.teams_frame.pack_forget()
        except Exception:
            pass
        # Show the players screen
        self.players_frame.pack(fill=tk.BOTH, expand=True)
        # Kick off a background scan to load players and teams
        self._start_scan()

    def show_teams(self):
        """Display the Teams screen and start scanning if necessary."""
        self.home_frame.pack_forget()
        self.players_frame.pack_forget()
        self.teams_frame.pack(fill=tk.BOTH, expand=True)
        # Kick off a scan if we don't have team names yet
        if not self.model.get_teams():
            # Use the same scanning logic as players
            if not self.scanning:
                self.scanning = True
                # Show scanning message in team screen
                self.team_scan_status_var.set("Scanning... please wait")
                threading.Thread(target=self._scan_teams_thread, daemon=True).start()
        else:
            # Update dropdown immediately
            teams = self.model.get_teams()
            self._update_team_dropdown(teams)
            # Auto‑select first team if none selected
            if teams and not self.team_edit_var.get():
                self.team_edit_var.set(teams[0])
                self._on_team_edit_selected()

    # -----------------------------------------------------------------
    # Randomizer
    # -----------------------------------------------------------------
    def _open_randomizer(self):
        """Open the Randomizer window for mass randomizing player values."""
        try:
            # Ensure we have up-to-date player and team lists
            self.model.refresh_players()
        except Exception:
            pass
        # Launch the randomizer window.  The RandomizerWindow class is
        # defined below.  It will build its own UI and handle
        # randomization logic.
        RandomizerWindow(self, self.model)

    def _open_team_shuffle(self) -> None:
        """Open the Team Shuffle window to shuffle players across selected teams."""
        try:
            # Refresh player list to ensure team assignments are current
            self.model.refresh_players()
        except Exception:
            pass
        TeamShuffleWindow(self, self.model)

    def _open_batch_edit(self) -> None:
        """
        Open the Batch Edit window to set a specific field across
        multiple players.  The BatchEditWindow allows selection of
        one or more teams, a category (Attributes, Tendencies,
        Durability, Vitals, Body, Badges, Contract, etc.), a field
        within that category, and a new value.  When executed, the
        specified value is written to the selected field for every
        player on the chosen teams.  Only live memory editing is
        supported; if the game process is not attached the user will
        be notified and no changes will occur.
        """
        try:
            # Refresh player and team lists; ignore errors if scanning fails
            self.model.refresh_players()
        except Exception:
            pass
        # Launch the batch edit window.  Any exceptions raised during
        # creation will be reported via a messagebox.
        try:
            BatchEditWindow(self, self.model)
        except Exception as exc:
            import traceback

            messagebox.showerror(
                "Batch Edit", f"Failed to open batch edit window: {exc}"
            )
            traceback.print_exc()

    def _open_2kcoy(self) -> None:
        """
        Automatically import player ratings from a fixed Google Sheet and apply
        them to the roster.  If ``COY_SHEET_ID`` is defined, this method
        downloads the CSV exports of the configured tabs and performs the
        import without prompting the user.  If downloading fails or the
        sheet ID is empty, the user will be prompted to select files
        manually.  A summary of updates and any players not found is
        displayed at the end.
        """
        # Refresh players to ensure we have up-to-date indices
        try:
            self.model.refresh_players()
        except Exception:
            pass
        # Require the game to be running
        if not self.model.mem.hproc:
            messagebox.showinfo(
                "2K COY Import",
                "NBA 2K25 does not appear to be running. Please launch the game and "
                "load a roster before importing.",
            )
            return

        # Ask the user which categories to import.  Present a simple
        # checkbox dialog so they can choose between Attributes,
        # Tendencies and Durability.  If they cancel or uncheck all
        # boxes, no import is performed.
        # ------------------------------------------------------------------
        categories_to_ask = ["Attributes", "Tendencies", "Durability"]
        try:
            dlg = CategorySelectionDialog(self, categories_to_ask)
            # Wait for the dialog to close before proceeding
            self.wait_window(dlg)
            selected_categories = dlg.selected
        except Exception:
            selected_categories = None
        # If the user cancelled (None) or selected nothing, abort
        if not selected_categories:
            return

        # Show a loading dialog to discourage clicking during processing
        loading_win = tk.Toplevel(self)
        loading_win.title("Loading")
        loading_win.geometry("350x120")
        loading_win.resizable(False, False)
        tk.Label(
            loading_win,
            text="Loading data... Please wait and do not click the updater.",
            wraplength=320,
            justify="left",
        ).pack(padx=20, pady=20)
        loading_win.update_idletasks()

        # Determine whether to auto-download or prompt for files
        auto_download = bool(COY_SHEET_ID)
        file_map: dict[str, str] = {}
        not_found: set[str] = set()

        if auto_download:
            # Attempt to fetch each configured sheet for the selected categories
            for cat, sheet_name in COY_SHEET_TABS.items():
                # Skip categories the user did not select
                if cat not in selected_categories:
                    continue
                try:
                    # Build CSV export URL for the given sheet
                    url = (
                        f"https://docs.google.com/spreadsheets/d/{COY_SHEET_ID}/"
                        f"gviz/tq?tqx=out:csv&sheet={urllib.parse.quote(sheet_name)}"
                    )
                    with urllib.request.urlopen(url, timeout=30) as resp:
                        csv_text = resp.read().decode("utf-8")
                except Exception:
                    csv_text = ""
                if not csv_text:
                    # Could not fetch this sheet; skip it
                    continue
                # Write the CSV text to a temporary file
                tmp = tempfile.NamedTemporaryFile(
                    delete=False, suffix=".csv", mode="w", encoding="utf-8"
                )
                tmp.write(csv_text)
                tmp.close()
                file_map[cat] = tmp.name
                # Parse names to identify missing players
                try:
                    import csv as _csv

                    reader = _csv.reader(io.StringIO(csv_text))
                    # Skip header row if present
                    next(reader, None)
                    for row in reader:
                        if not row:
                            continue
                        name = row[0].strip()
                        if not name:
                            continue
                        idxs = self.model.find_player_indices_by_name(name)
                        if not idxs:
                            not_found.add(name)
                except Exception:
                    pass
        # If no files were downloaded or auto-download disabled, prompt the user
        if not file_map:
            # Ask for the Attributes file
            # For manual selection, prompt only for the categories chosen

            # Helper to open a file dialog for a given category
            def prompt_file(cat_name: str) -> str:
                return filedialog.askopenfilename(
                    title=f"Select {cat_name} Import File",
                    filetypes=[
                        ("Delimited files", "*.csv *.tsv *.txt"),
                        ("All files", "*.*"),
                    ],
                )

            # For each selected category ask the user to select a file.  If
            # they cancel on the first mandatory category (Attributes) then
            # abort.
            for cat in categories_to_ask:
                if cat not in selected_categories:
                    continue
                path = prompt_file(cat)
                if not path:
                    # User cancelled; abort the entire import
                    # Remove any previously selected files
                    file_map.clear()
                    return
                file_map[cat] = path

            # Collect names from selected files
            def collect_missing_names(path: str) -> None:
                import csv as _csv

                if not path or not os.path.isfile(path):
                    return
                try:
                    with open(path, "r", encoding="utf-8", errors="ignore") as f:
                        sample = f.readline()
                        delim = (
                            "\t" if "\t" in sample else "," if "," in sample else ";"
                        )
                        f.seek(0)
                        reader = _csv.reader(f, delimiter=delim)
                        next(reader, None)  # skip header
                        for row in reader:
                            if not row:
                                continue
                            name = row[0].strip()
                            if not name:
                                continue
                            idxs = self.model.find_player_indices_by_name(name)
                            if not idxs:
                                not_found.add(name)
                except Exception:
                    pass

            for p in file_map.values():
                collect_missing_names(p)

        # Compute the size of the Attributes player pool (number of names in the
        # attributes file).  We track this to inform the user if some
        # players were not updated.  It is computed before imports so
        # that ``import_all`` does not need to be changed.
        attr_pool_size = 0
        attr_names_set: set[str] = set()
        if "Attributes" in file_map:
            try:
                import csv as _csv

                path = file_map["Attributes"]
                # Read the file (auto‑determine delimiter similar to import_table)
                with open(path, "r", encoding="utf-8", errors="ignore") as f:
                    sample = f.readline()
                    delim = "\t" if "\t" in sample else "," if "," in sample else ";"
                    f.seek(0)
                    reader = _csv.reader(f, delimiter=delim)
                    rows = list(reader)
                # Skip header and collect non‑blank names
                for row in rows[1:]:
                    if not row or not row[0].strip():
                        continue
                    attr_names_set.add(row[0].strip())
                attr_pool_size = len(attr_names_set)
            except Exception:
                attr_pool_size = 0
        # Perform imports only for the selected categories
        results = self.model.import_all(file_map)
        # Refresh players to reflect changes
        try:
            self.model.refresh_players()
        except Exception:
            pass
        # Remove any temporary files created during auto-download
        if auto_download:
            for p in file_map.values():
                try:
                    if p and os.path.isfile(p):
                        os.remove(p)
                except Exception:
                    pass
        # Build summary
        msg_lines = ["2K COY import completed."]
        # If any players were updated, list counts per category
        if results:
            msg_lines.append("\nPlayers updated:")
            for cat, cnt in results.items():
                if file_map.get(cat):
                    msg_lines.append(f"  {cat}: {cnt}")
        # Compute number of attributes pool entries that were not updated
        if attr_pool_size:
            updated_attr = results.get("Attributes", 0)
            # Count only those not_found names that originated from the
            # attributes file
            if attr_names_set and not_found:
                not_matched = len(attr_names_set.intersection(not_found))
            else:
                not_matched = 0
            not_updated = attr_pool_size - updated_attr - not_matched
            if not_updated > 0:
                msg_lines.append(
                    f"\n{not_updated} player{'s' if not_updated != 1 else ''} in the Attributes pool "
                    f"could not be updated (blank values or no matching fields)."
                )
        # List any players that were not found in the roster
        if not_found:
            msg_lines.append("\nPlayers not found (no matches in roster):")
            for name in sorted(not_found):
                msg_lines.append(f"  {name}")
        else:
            msg_lines.append("\nAll players were found in the roster.")
        # Destroy the loading dialog before showing the summary
        try:
            loading_win.destroy()
        except Exception:
            pass
        messagebox.showinfo("2K COY Import", "\n".join(msg_lines))

    def _open_load_excel(self) -> None:
        """
        Prompt the user to import player updates from a single Excel workbook.

        This method first asks the user to select an Excel (.xlsx/.xls) file.
        After selecting the file, it presents a category selection dialog
        allowing the user to choose which types of data to import (Attributes,
        Tendencies and/or Durability).  For each selected category, the
        corresponding sheet is extracted from the workbook (matching the
        category name if it exists, otherwise falling back to the first sheet).
        The sheet is converted to a temporary CSV file and passed through
        ``import_all`` for processing.  A modal loading dialog is displayed
        during the import to discourage further clicks.
        """
        # Refresh players to ensure we have up-to-date indices
        try:
            self.model.refresh_players()
        except Exception:
            pass
        # Require the game to be running
        if not self.model.mem.hproc:
            messagebox.showinfo(
                "Excel Import",
                "NBA 2K25 does not appear to be running. Please launch the game and "
                "load a roster before importing.",
            )
            return
        # Prompt for the Excel workbook first
        workbook_path = filedialog.askopenfilename(
            title="Select Excel Workbook",
            filetypes=[("Excel files", "*.xlsx *.xls"), ("All files", "*.*")],
        )
        if not workbook_path:
            return
        # Ask the user which categories to import
        categories_to_ask = ["Attributes", "Tendencies", "Durability"]
        try:
            dlg = CategorySelectionDialog(self, categories_to_ask)
            self.wait_window(dlg)
            selected_categories = dlg.selected
        except Exception:
            selected_categories = None
        if not selected_categories:
            return
        # Show a loading dialog to discourage clicking during processing
        loading_win = tk.Toplevel(self)
        loading_win.title("Loading")
        loading_win.geometry("350x120")
        loading_win.resizable(False, False)
        tk.Label(
            loading_win,
            text="Loading data... Please wait and do not click the updater.",
            wraplength=320,
            justify="left",
        ).pack(padx=20, pady=20)
        loading_win.update_idletasks()
        file_map: dict[str, str] = {}
        not_found: set[str] = set()
        import pandas as _pd

        # Helper to collect missing names from a DataFrame
        def collect_missing_names_df(df) -> None:
            for name in df.iloc[:, 0].astype(str).str.strip():
                if not name:
                    continue
                idxs = self.model.find_player_indices_by_name(name)
                if not idxs:
                    not_found.add(name)

        try:
            # Read the workbook once to obtain the list of sheet names
            try:
                xls = _pd.ExcelFile(workbook_path)
            except Exception:
                messagebox.showerror(
                    "Excel Import", f"Failed to read {os.path.basename(workbook_path)}"
                )
                loading_win.destroy()
                return
            for cat in categories_to_ask:
                if cat not in selected_categories:
                    continue
                # Determine which sheet to read: prefer exact match of category name
                sheet_to_use = None
                for sheet_name in xls.sheet_names:
                    if sheet_name.strip().lower() == cat.lower():
                        sheet_to_use = sheet_name
                        break
                # If no exact match, use the first sheet
                if sheet_to_use is None:
                    sheet_to_use = xls.sheet_names[0] if xls.sheet_names else None
                if sheet_to_use is None:
                    continue
                # Read the sheet into a DataFrame
                try:
                    df = xls.parse(sheet_to_use)
                except Exception:
                    # Attempt to read via pandas.read_excel fallback
                    try:
                        df = _pd.read_excel(workbook_path, sheet_name=sheet_to_use)
                    except Exception:
                        df = None
                if df is None:
                    continue
                # Write DataFrame to a temporary CSV file
                tmp = tempfile.NamedTemporaryFile(
                    delete=False, suffix=".csv", mode="w", encoding="utf-8"
                )
                df.to_csv(tmp.name, index=False)
                tmp.close()
                file_map[cat] = tmp.name
                collect_missing_names_df(df)
            # Perform the import
            results = self.model.import_all(file_map)
            # Refresh players to reflect changes
            try:
                self.model.refresh_players()
            except Exception:
                pass
        finally:
            # Destroy the loading dialog
            try:
                loading_win.destroy()
            except Exception:
                pass
            # Clean up temporary files
            for p in file_map.values():
                try:
                    if p and os.path.isfile(p):
                        os.remove(p)
                except Exception:
                    pass
        # Build summary message
        msg_lines = ["Excel import completed."]
        if results:
            msg_lines.append("\nPlayers updated:")
            for cat, cnt in results.items():
                if file_map.get(cat):
                    msg_lines.append(f"  {cat}: {cnt}")
        # Inform about missing players
        if not_found:
            msg_lines.append("\nPlayers not found:")
            for name in sorted(not_found):
                msg_lines.append(f"  {name}")
        messagebox.showinfo("Excel Import", "\n".join(msg_lines))

    # ---------------------------------------------------------------------
    # Teams screen
    # ---------------------------------------------------------------------
    def _build_teams_screen(self):
        """Construct the Teams editing screen."""
        self.teams_frame = tk.Frame(self, bg="#F5F5F5")
        # Top bar with team selection
        top = tk.Frame(self.teams_frame, bg="#F5F5F5")
        top.pack(side=tk.TOP, fill=tk.X, pady=10, padx=10)
        tk.Label(
            top, text="Team:", font=("Segoe UI", 12), bg="#F5F5F5", fg="#2F3E46"
        ).pack(side=tk.LEFT)
        self.team_edit_var = tk.StringVar()
        self.team_edit_dropdown = ttk.Combobox(
            top, textvariable=self.team_edit_var, state="readonly"
        )
        self.team_edit_dropdown.bind(
            "<<ComboboxSelected>>", self._on_team_edit_selected
        )
        self.team_edit_dropdown.pack(side=tk.LEFT, padx=5)
        # Scan status label for teams
        self.team_scan_status_var = tk.StringVar()
        self.team_scan_status_label = tk.Label(
            top,
            textvariable=self.team_scan_status_var,
            font=("Segoe UI", 10, "italic"),
            bg="#F5F5F5",
            fg="#52796F",
        )
        self.team_scan_status_label.pack(side=tk.LEFT, padx=10)
        # Detail pane for team fields
        detail = tk.Frame(self.teams_frame, bg="#FFFFFF", relief=tk.RIDGE, bd=1)
        detail.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        tk.Label(
            detail,
            text="Team Details",
            font=("Segoe UI", 14, "bold"),
            bg="#FFFFFF",
            fg="#2F3E46",
        ).pack(pady=(5, 10))
        # Form for each team field
        self.team_field_vars: Dict[str, tk.StringVar] = {}
        form = tk.Frame(detail, bg="#FFFFFF")
        form.pack(fill=tk.X, padx=10, pady=5)
        row = 0
        for label in TEAM_FIELDS.keys():
            tk.Label(form, text=f"{label}:", bg="#FFFFFF").grid(
                row=row, column=0, sticky=tk.W, pady=2
            )
            var = tk.StringVar()
            entry = tk.Entry(form, textvariable=var)
            entry.grid(row=row, column=1, sticky=tk.EW, padx=5, pady=2)
            self.team_field_vars[label] = var
            row += 1
        form.columnconfigure(1, weight=1)
        # Save button
        self.btn_team_save = tk.Button(
            detail,
            text="Save",
            command=self._save_team,
            bg="#84A98C",
            fg="white",
            relief=tk.FLAT,
            state=tk.DISABLED,
        )
        self.btn_team_save.pack(pady=10)

    def _scan_teams_thread(self):
        """Background thread to refresh players and teams for the Teams screen."""
        # Use the same refresh mechanism as players
        self.model.refresh_players()
        teams = self.model.get_teams()

        def update_ui():
            self.scanning = False
            self.team_scan_status_var.set("")
            self._update_team_dropdown(teams)
            # Auto‑select first team if available
            if teams:
                self.team_edit_var.set(teams[0])
                self._on_team_edit_selected()

        self.after(0, update_ui)

    # ---------------------------------------------------------------------
    def _update_team_dropdown(self, teams: list[str]):
        """Helper to update both team dropdowns (players and teams screens)."""
        # Update players screen dropdown if it exists
        if hasattr(self, "team_dropdown"):
            self.team_dropdown["values"] = teams
            if teams:
                self.team_var.set(teams[0])
        # Update teams screen dropdown
        self.team_edit_dropdown["values"] = teams

    def _on_team_edit_selected(self, _event=None):
        """Load team field values when a team is selected."""
        team_name = self.team_edit_var.get()
        if not team_name:
            self.btn_team_save.config(state=tk.DISABLED)
            for var in self.team_field_vars.values():
                var.set("")
            return
        # Find team index
        teams = self.model.get_teams()
        try:
            idx = teams.index(team_name)
        except ValueError:
            self.btn_team_save.config(state=tk.DISABLED)
            return
        fields = self.model.get_team_fields(idx)
        if fields is None:
            # Not connected or cannot read
            for var in self.team_field_vars.values():
                var.set("")
            self.btn_team_save.config(state=tk.DISABLED)
            return
        # Populate fields
        for label, var in self.team_field_vars.items():
            val = fields.get(label, "")
            var.set(val)
        # Enable save if process open
        self.btn_team_save.config(
            state=tk.NORMAL if self.model.mem.hproc else tk.DISABLED
        )

    def _save_team(self):
        """Save the edited team fields back to memory."""
        team_name = self.team_edit_var.get()
        if not team_name:
            return
        teams = self.model.get_teams()
        try:
            idx = teams.index(team_name)
        except ValueError:
            return
        values = {label: var.get() for label, var in self.team_field_vars.items()}
        ok = self.model.set_team_fields(idx, values)
        if ok:
            messagebox.showinfo("Success", f"Updated {team_name} successfully.")
            # Refresh team list to reflect potential name change
            self.model.refresh_players()
            teams = self.model.get_teams()
            self._update_team_dropdown(teams)
            # Reselect the updated team name if changed
            if values.get("Team Name"):
                self.team_edit_var.set(values.get("Team Name"))
        else:
            messagebox.showerror(
                "Error",
                "Failed to write team data. Make sure the game is running and try again.",
            )

    # ---------------------------------------------------------------------
    # Home helpers
    # ---------------------------------------------------------------------
    def _update_status(self):
        if self.model.mem.open_process():
            pid = self.model.mem.pid
            self.status_var.set(f"NBA2K25 is running (PID {pid})")
        else:
            self.status_var.set("NBA2K25 not detected")

    # ---------------------------------------------------------------------
    # Scanning players
    # ---------------------------------------------------------------------
    def _start_scan(self):
        if self.scanning:
            return
        self.scanning = True
        self.player_listbox.delete(0, tk.END)
        self.player_listbox.insert(tk.END, "Scanning players...")
        self.scan_status_label.config(text="Scanning... please wait")
        # Launch in a separate thread to avoid blocking UI
        threading.Thread(target=self._scan_thread, daemon=True).start()

    def _scan_thread(self):
        self.model.refresh_players()
        teams = self.model.get_teams()

        def update_ui():
            self.scanning = False
            # Update both dropdowns via helper
            self._update_team_dropdown(teams)
            if teams:
                self.team_var.set(teams[0])
            else:
                self.team_var.set("")
            self._refresh_player_list()
            self.scan_status_label.config(text="")

        self.after(0, update_ui)

    # ---------------------------------------------------------------------
    # UI update helpers
    # ---------------------------------------------------------------------
    def _refresh_player_list(self):
        team = self.team_var.get()
        # Get the players for the selected team.  Store them in
        # ``current_players`` so the search filter can operate on
        # a stable list without hitting the model repeatedly.
        self.current_players = self.model.get_players_by_team(team) if team else []
        # Apply search filtering.  This will rebuild the listbox and
        # update ``filtered_player_indices``.  If no search term is set
        # (i.e. placeholder text), all players are displayed.
        self._filter_player_list()
        # Reset selection and detail fields
        self.selected_player = None
        self._update_detail_fields()

    def _filter_player_list(self) -> None:
        """Filter the player list based on the search entry and repopulate the listbox.

        This method examines the text in ``self.player_search_var``.  If the
        search field contains only the placeholder or is empty, all players
        in ``current_players`` are shown.  Otherwise, only players whose
        full name contains the search string (case‑insensitive) will be
        displayed.  ``filtered_player_indices`` is updated to map each
        visible row back to the index in ``current_players``.
        """
        search = self.player_search_var.get().strip().lower()
        # Treat the placeholder text as an empty search
        if search == "search players…".lower():
            search = ""
        self.player_listbox.delete(0, tk.END)
        self.filtered_player_indices = []
        for idx, p in enumerate(self.current_players):
            name = (p.full_name or "").lower()
            if not search or search in name:
                self.filtered_player_indices.append(idx)
                self.player_listbox.insert(tk.END, p.full_name)

    def _on_team_selected(self, _event=None):
        self._refresh_player_list()

    def _on_player_selected(self, _event=None):
        selection = self.player_listbox.curselection()
        if not selection:
            self.selected_player = None
        else:
            idx = selection[0]
            # Map the visible index back to the index within
            # ``current_players`` using ``filtered_player_indices``.  If the
            # mapping is out of range, clear the selection.
            if idx < len(self.filtered_player_indices):
                p_idx = self.filtered_player_indices[idx]
                if p_idx < len(self.current_players):
                    self.selected_player = self.current_players[p_idx]
                else:
                    self.selected_player = None
            else:
                self.selected_player = None
        self._update_detail_fields()

    def _update_detail_fields(self):
        p = self.selected_player
        if not p:
            # Clear fields
            self.var_first.set("")
            self.var_last.set("")
            self.var_face.set("")
            self.var_player_team.set("")
            self.btn_save.config(state=tk.DISABLED)
            self.btn_edit.config(state=tk.DISABLED)
        else:
            self.var_first.set(p.first_name)
            self.var_last.set(p.last_name)
            self.var_face.set(str(p.face_id))
            self.var_player_team.set(p.team)
            # Save button enabled only if connected to the game
            enable_save = self.model.mem.hproc is not None
            self.btn_save.config(state=tk.NORMAL if enable_save else tk.DISABLED)
            self.btn_edit.config(state=tk.NORMAL)
            # Copy button enabled if connected.  We
            # defer determining actual destination availability until the
            # copy dialog is opened.
            enable_copy = enable_save and p is not None
            self.btn_copy.config(state=tk.NORMAL if enable_copy else tk.DISABLED)

    # ---------------------------------------------------------------------
    # Saving and editing
    # ---------------------------------------------------------------------
    def _save_player(self):
        p = self.selected_player
        if not p:
            return
        # Update from entry fields
        p.first_name = self.var_first.get().strip()
        p.last_name = self.var_last.get().strip()
        try:
            p.face_id = int(self.var_face.get())
        except ValueError:
            messagebox.showerror("Invalid value", "Face ID must be an integer")
            return
        try:
            self.model.update_player(p)
            messagebox.showinfo("Success", "Player updated successfully")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save changes:\n{e}")
        # Refresh list to reflect potential name changes
        self._refresh_player_list()

    def _open_full_editor(self):
        p = self.selected_player
        if not p:
            return
        editor = FullPlayerEditor(self, p, self.model)
        editor.grab_set()

    def _open_copy_dialog(self):
        """Open a dialog allowing the user to copy data from the selected player to another."""
        src = self.selected_player
        if not src:
            return
        # Prepare list of destination players (exclude source)
        if self.model.fallback_players:
            # Fallback mode: use loaded players list
            dest_players = [p for p in self.model.players if p.index != src.index]
        else:
            # Live memory mode: scan players across all teams via roster pointers
            dest_players: list[Player] = []
            for idx, _ in self.model.team_list:
                players = self.model.scan_team_players(idx)
                for p in players:
                    if p.index != src.index:
                        dest_players.append(p)
        # Remove duplicate names (based on index) while preserving order
        seen = set()
        uniq_dest = []
        for p in dest_players:
            if p.index not in seen:
                seen.add(p.index)
                uniq_dest.append(p)
        dest_players = uniq_dest
        if not dest_players:
            messagebox.showinfo(
                "Copy Player Data", "No other players are available to copy to."
            )
            return
        # Create dialog window
        win = tk.Toplevel(self)
        win.title("Copy Player Data")
        win.geometry("400x320")
        win.resizable(False, False)
        win.transient(self)
        win.grab_set()
        # Source label
        tk.Label(
            win, text=f"Copy from: {src.full_name}", font=("Segoe UI", 12, "bold")
        ).pack(pady=(10, 5))
        # Destination dropdown
        dest_var = tk.StringVar()
        dest_names = [p.full_name for p in dest_players]
        dest_map = {p.full_name: p for p in dest_players}
        dest_frame = tk.Frame(win)
        dest_frame.pack(fill=tk.X, padx=20, pady=(0, 10))
        tk.Label(dest_frame, text="Copy to:", font=("Segoe UI", 10)).pack(side=tk.LEFT)
        dest_combo = ttk.Combobox(
            dest_frame, textvariable=dest_var, values=dest_names, state="readonly"
        )
        dest_combo.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 0))
        if dest_names:
            dest_var.set(dest_names[0])
        # Category checkboxes
        chk_frame = tk.Frame(win)
        chk_frame.pack(fill=tk.X, padx=20, pady=(5, 10))
        tk.Label(chk_frame, text="Data to copy:", font=("Segoe UI", 10)).pack(
            anchor=tk.W
        )
        var_full = tk.IntVar(value=0)
        var_appearance = tk.IntVar(value=0)
        var_attributes = tk.IntVar(value=0)
        var_tendencies = tk.IntVar(value=0)
        var_badges = tk.IntVar(value=0)
        cb1 = tk.Checkbutton(chk_frame, text="Full Player", variable=var_full)
        cb2 = tk.Checkbutton(chk_frame, text="Appearance", variable=var_appearance)
        cb3 = tk.Checkbutton(chk_frame, text="Attributes", variable=var_attributes)
        cb4 = tk.Checkbutton(chk_frame, text="Tendencies", variable=var_tendencies)
        cb5 = tk.Checkbutton(chk_frame, text="Badges", variable=var_badges)
        cb1.pack(anchor=tk.W)
        cb2.pack(anchor=tk.W)
        cb3.pack(anchor=tk.W)
        cb4.pack(anchor=tk.W)
        cb5.pack(anchor=tk.W)
        # Buttons for copy/cancel
        btn_frame = tk.Frame(win)
        btn_frame.pack(pady=10)

        def do_copy():
            dest_name = dest_var.get()
            dest_player = dest_map.get(dest_name)
            if not dest_player:
                messagebox.showerror(
                    "Copy Player Data", "No destination player selected."
                )
                return
            categories = []
            if var_full.get():
                categories = ["full"]
            else:
                if var_appearance.get():
                    categories.append("appearance")
                if var_attributes.get():
                    categories.append("attributes")
                if var_tendencies.get():
                    categories.append("tendencies")
                if var_badges.get():
                    categories.append("badges")
            if not categories:
                messagebox.showwarning(
                    "Copy Player Data",
                    "Please select at least one data category to copy.",
                )
                return
            success = self.model.copy_player_data(
                src.index, dest_player.index, categories
            )
            if success:
                messagebox.showinfo("Copy Player Data", "Data copied successfully.")
                # Refresh the player list to reflect any changes
                self._start_scan()
            else:
                messagebox.showerror(
                    "Copy Player Data",
                    "Failed to copy data. Make sure the game is running and try again.",
                )
            win.destroy()

        tk.Button(
            btn_frame,
            text="Copy",
            command=do_copy,
            bg="#84A98C",
            fg="white",
            relief=tk.FLAT,
        ).pack(side=tk.LEFT, padx=5)
        tk.Button(
            btn_frame,
            text="Cancel",
            command=win.destroy,
            bg="#B0413E",
            fg="white",
            relief=tk.FLAT,
        ).pack(side=tk.LEFT, padx=5)

    def _open_import_dialog(self):
        """Prompt the user to select one or more import files and apply them to the roster.

        The user can select up to three files corresponding to Attributes,
        Tendencies, and Durability tables.  The method attempts to
        auto‑detect the category of each selected file based on the
        column headers.  If no recognizable category is detected, the
        file is ignored.  After importing, the player list is refreshed.

        """
        # Prompt for files; allow multiple selection.  If the user cancels,
        # return immediately.
        paths = filedialog.askopenfilenames(
            parent=self,
            title="Select Import Files",
            filetypes=[("Data files", "*.txt *.csv *.tsv"), ("All files", "*.*")],
        )
        if not paths:
            return
        # Precompute normalized header names for each known category
        attr_norms = [self.model._normalize_header_name(h) for h in ATTR_IMPORT_ORDER]
        tend_norms = [self.model._normalize_header_name(h) for h in TEND_IMPORT_ORDER]
        dur_norms = [self.model._normalize_header_name(h) for h in DUR_IMPORT_ORDER]
        file_map: dict[str, str] = {}
        for path in paths:
            # Read the first line of the file to inspect headers
            try:
                with open(path, "r", encoding="utf-8", errors="ignore") as f:
                    first_line = f.readline()
            except Exception:
                continue
            # Detect delimiter: prioritize tab, then comma, then semicolon
            delim = "\t" if "\t" in first_line else "," if "," in first_line else ";"
            header = [h.strip() for h in first_line.strip().split(delim)]
            # Normalize all headers except the first (player name)
            headers_norm = (
                [self.model._normalize_header_name(h) for h in header[1:]]
                if len(header) > 1
                else []
            )
            # Compute match scores for each category
            score_attr = sum(
                1
                for h in headers_norm
                if any(nf == h or nf in h or h in nf for nf in attr_norms)
            )
            score_tend = sum(
                1
                for h in headers_norm
                if any(nf == h or nf in h or h in nf for nf in tend_norms)
            )
            score_dur = sum(
                1
                for h in headers_norm
                if any(nf == h or nf in h or h in nf for nf in dur_norms)
            )
            # Determine category with the highest score
            if score_attr >= score_tend and score_attr >= score_dur and score_attr > 0:
                cat = "Attributes"
            elif (
                score_tend >= score_attr and score_tend >= score_dur and score_tend > 0
            ):
                cat = "Tendencies"
            elif score_dur >= score_attr and score_dur >= score_tend and score_dur > 0:
                cat = "Durability"
            else:
                # Could not determine category; skip this file
                continue
            # If this category is not yet mapped, assign the file path
            if cat not in file_map:
                file_map[cat] = path
        if not file_map:
            messagebox.showerror(
                "Import Data",
                "The selected file(s) do not match any known data category.",
            )
            return
        # Invoke the import for all detected categories
        results = self.model.import_all(file_map)
        # Compose a summary message
        messages = []
        for cat in ["Attributes", "Tendencies", "Durability"]:
            if cat in file_map:
                count = results.get(cat, 0)
                basename = os.path.basename(file_map[cat])
                messages.append(f"Imported {count} players for {cat} from {basename}.")
        msg = "\n".join(messages) if messages else "No data was imported."
        messagebox.showinfo("Import Data", msg)
        # Refresh players to reflect imported values (works only when process is open)
        self._start_scan()


class FullPlayerEditor(tk.Toplevel):
    """A tabbed editor window for advanced player attributes."""

    def __init__(self, parent: tk.Tk, player: Player, model: PlayerDataModel):
        super().__init__(parent)
        self.player = player
        self.model = model
        self.title(f"Editing: {player.full_name}")
        # Dimensions: slightly larger for many fields
        self.geometry("700x500")
        # Track which fields changed so we can enable Save/Apply
        self._unsaved_changes = set()
        # Dictionary mapping category names to a mapping of field names to
        # Tkinter variables.  This allows us to load and save values easily.
        self.field_vars: dict[str, dict[str, tk.Variable]] = {}
        # Dictionary mapping (category_name, field_name) -> metadata dict
        # describing offset, start bit and bit length.  Using the tuple
        # avoids using unhashable Tkinter variables as keys.
        self.field_meta: dict[tuple[str, str], dict[str, int]] = {}

        # Dictionary to hold Spinbox widgets for each field.  The key is
        # (category_name, field_name) and the value is the Spinbox
        # instance.  Storing these allows us to compute min/max values
        # dynamically based on the widget’s configuration (e.g. range)
        # when adjusting entire categories via buttons.
        self.spin_widgets: dict[tuple[str, str], tk.Spinbox] = {}
        # Notebook for category tabs
        notebook = ttk.Notebook(self)
        notebook.pack(fill=tk.BOTH, expand=True)
        # Determine which categories are available from the model.  If
        # categories are missing, we still display the tab with a placeholder.
        # Determine tab order.  Start with the common categories defined in
        # the offset map.  Then append any additional categories found in
        # the model that are not already listed.  Finally include
        # placeholder tabs for future extensions (Accessories, Contract).
        categories = []
        for name in ["Body", "Vitals", "Attributes", "Tendencies", "Badges"]:
            categories.append(name)
        # Append any additional category names defined in the model
        for name in self.model.categories.keys():
            if name not in categories:
                categories.append(name)
        # Append placeholder categories for unimplemented sections
        for name in ["Accessories", "Contract"]:
            if name not in categories:
                categories.append(name)
        for cat in categories:
            frame = tk.Frame(notebook, bg="#F5F5F5")
            notebook.add(frame, text=cat)
            self._build_category_tab(frame, cat)
        # Action buttons at bottom
        btn_frame = tk.Frame(self, bg="#F5F5F5")
        btn_frame.pack(fill=tk.X, pady=5)
        save_btn = tk.Button(
            btn_frame,
            text="Save",
            command=self._save_all,
            bg="#84A98C",
            fg="white",
            relief=tk.FLAT,
        )
        save_btn.pack(side=tk.LEFT, padx=10)
        close_btn = tk.Button(
            btn_frame,
            text="Close",
            command=self.destroy,
            bg="#B0413E",
            fg="white",
            relief=tk.FLAT,
        )
        close_btn.pack(side=tk.LEFT)
        # Populate field values from memory
        self._load_all_values()

    def _build_category_tab(self, parent: tk.Frame, category_name: str) -> None:
        """
        Build the UI for a specific category.  If field definitions are
        available for the category, create a grid of labels and spinboxes
        for each field.  Otherwise, display a placeholder message.
        """
        fields = self.model.categories.get(category_name, [])
        # Add category-level adjustment buttons for Attributes, Durability, and Tendencies
        if category_name in ("Attributes", "Durability", "Tendencies"):
            btn_frame = tk.Frame(parent, bg="#F5F5F5")
            btn_frame.pack(fill=tk.X, padx=10, pady=(5, 0))
            actions = [
                ("Min", "min"),
                ("+5", "plus5"),
                ("+10", "plus10"),
                ("-5", "minus5"),
                ("-10", "minus10"),
                ("Max", "max"),
            ]
            for label, action in actions:
                tk.Button(
                    btn_frame,
                    text=label,
                    command=lambda act=action, cat=category_name: self._adjust_category(
                        cat, act
                    ),
                    bg="#52796F",
                    fg="white",
                    relief=tk.FLAT,
                    width=5,
                ).pack(side=tk.LEFT, padx=2)
        # Container for scrolled view if many fields
        canvas = tk.Canvas(parent, bg="#F5F5F5", highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#F5F5F5")
        scroll_frame.bind(
            "<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        # Pack canvas and scrollbar
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        # Save variables mapping
        self.field_vars.setdefault(category_name, {})
        if not fields:
            # No definitions found
            tk.Label(
                scroll_frame,
                text=f"{category_name} editing not available.",
                bg="#F5F5F5",
                fg="#6C757D",
            ).pack(padx=10, pady=10)
            return
        # Build rows for each field
        for row, field in enumerate(fields):
            name = field.get("name", f"Field {row}")
            offset_str = field.get("offset", "0")
            # Convert hex or int string to int
            try:
                offset_val = int(offset_str, 16)
            except Exception:
                offset_val = int(offset_str) if offset_str else 0
            start_bit = int(field.get("startBit", 0))
            length = int(field.get("length", 8))
            # Label
            lbl = tk.Label(scroll_frame, text=name + ":", bg="#F5F5F5")
            lbl.grid(row=row, column=0, sticky=tk.W, padx=(10, 5), pady=2)
            # Variable and spinbox
            var = tk.IntVar(value=0)
            # Determine raw maximum value for the bitfield
            max_raw = (1 << length) - 1
            # Compute the range shown in the spinbox.  For Attributes
            # categories we convert the raw 0..max_raw values to the 2K
            # rating scale of 25..99.  This mapping is handled in
            # _load_all_values/_save_all; here we restrict the spinbox
            # range to reflect the rating bounds.  For all other
            # categories we use the raw bit range.
            # Determine the displayed range of the Spinbox.  For
            # Attributes, Durability and Tendencies we display the
            # familiar 25..99 rating scale.  Conversion to/from raw
            # bitfield values is handled in the load/save methods.  For
            # all other categories, use the raw bit range.
            if category_name in ("Attributes", "Durability"):
                # Attributes and Durability use the familiar 25–99 rating scale
                spin_from = 25
                spin_to = 99
            elif category_name == "Tendencies":
                # Tendencies are displayed on a 0–100 scale
                spin_from = 0
                spin_to = 100
            else:
                spin_from = 0
                spin_to = max_raw
            # Determine if this field has an enumeration of values defined.
            # If the field contains a "values" list, we use a combobox
            # populated with those values.  Otherwise we fall back to
            # category‑specific handling (badges) or a numeric spinbox.
            values_list = field.get("values") if isinstance(field, dict) else None
            if values_list:
                # Create an IntVar to store the selected index
                var = tk.IntVar(value=0)
                combo = ttk.Combobox(
                    scroll_frame,
                    values=values_list,
                    state="readonly",
                    width=16,
                )
                combo.grid(row=row, column=1, sticky=tk.W, padx=(0, 10), pady=2)

                # When user picks an entry, update the IntVar accordingly
                def on_enum_selected(_event, v=var, c=combo, vals=values_list):
                    try:
                        v.set(vals.index(c.get()))
                    except Exception:
                        v.set(0)

                combo.bind("<<ComboboxSelected>>", on_enum_selected)
                # Store variable
                self.field_vars[category_name][name] = var
                # Record metadata; keep reference to combobox and values list
                self.field_meta[(category_name, name)] = {
                    "offset": offset_val,
                    "start_bit": start_bit,
                    "length": length,
                    "widget": combo,
                    "values": values_list,
                }

                # Flag unsaved changes
                def on_enum_change(*args, cat=category_name, field_name=name):
                    self._unsaved_changes.add((cat, field_name))

                var.trace_add("write", on_enum_change)
            elif category_name == "Badges":
                # Special handling for badge levels: expose a human‑readable
                # combobox instead of a numeric spinbox.  Each badge uses a
                # 3‑bit field (0–7) but the game recognises only 0..4.
                var = tk.IntVar(value=0)
                combo = ttk.Combobox(
                    scroll_frame,
                    values=BADGE_LEVEL_NAMES,
                    state="readonly",
                    width=12,
                )
                combo.grid(row=row, column=1, sticky=tk.W, padx=(0, 10), pady=2)

                # When the user picks a level, update the IntVar
                def on_combo_selected(_event, v=var, c=combo):
                    val_name = c.get()
                    v.set(BADGE_NAME_TO_VALUE.get(val_name, 0))

                combo.bind("<<ComboboxSelected>>", on_combo_selected)
                # Store variable for this field
                self.field_vars[category_name][name] = var
                # Record metadata; also keep reference to combobox for later update
                self.field_meta[(category_name, name)] = {
                    "offset": offset_val,
                    "start_bit": start_bit,
                    "length": length,
                    "widget": combo,
                }

                # Flag unsaved changes
                def on_badge_change(*args, cat=category_name, field_name=name):
                    self._unsaved_changes.add((cat, field_name))

                var.trace_add("write", on_badge_change)
            else:
                # Use Spinbox for numeric values; large ranges may be unwieldy
                spin = tk.Spinbox(
                    scroll_frame,
                    from_=spin_from,
                    to=spin_to,
                    textvariable=var,
                    width=10,
                )
                spin.grid(row=row, column=1, sticky=tk.W, padx=(0, 10), pady=2)
                # Store variable by name for this category
                self.field_vars[category_name][name] = var
                # Record metadata keyed by (category, field_name)
                self.field_meta[(category_name, name)] = {
                    "offset": offset_val,
                    "start_bit": start_bit,
                    "length": length,
                    "widget": spin,
                }
                # Save the Spinbox widget for later category-wide adjustments
                self.spin_widgets[(category_name, name)] = spin

                # Flag unsaved changes when the value changes
                def on_spin_change(*args, cat=category_name, field_name=name):
                    self._unsaved_changes.add((cat, field_name))

                var.trace_add("write", on_spin_change)

    def _load_all_values(self) -> None:
        """
        Populate all spinboxes with current values from memory.  This
        iterates over the categories and fields stored in
        ``self.field_vars`` and calls ``model.get_field_value`` for
        each one.
        """
        # Iterate over each category and field to load values using stored
        # metadata.  The metadata is stored in ``self.field_meta`` keyed by
        # (category, field_name).  We then set the associated variable.
        for category, fields in self.field_vars.items():
            for field_name, var in fields.items():
                meta = self.field_meta.get((category, field_name))
                if not meta:
                    continue
                offset = meta.get("offset", 0)
                start_bit = meta.get("start_bit", 0)
                length = meta.get("length", 0)
                value = self.model.get_field_value(
                    self.player.index, offset, start_bit, length
                )
                if value is not None:
                    try:
                        # Convert raw bitfield values to user‑friendly values
                        if category in ("Attributes", "Durability"):
                            # Map the raw bitfield value into the 25–99 rating scale
                            rating = convert_raw_to_rating(int(value), length)
                            var.set(int(rating))
                        elif category == "Tendencies":
                            # Tendencies use a 0–100 scale
                            rating = convert_tendency_raw_to_rating(int(value), length)
                            var.set(int(rating))
                        elif category == "Badges":
                            # Badges are stored as 3‑bit fields; clamp to 0–4
                            lvl = int(value)
                            if lvl < 0:
                                lvl = 0
                            elif lvl > 4:
                                lvl = 4
                            var.set(lvl)
                            # Update combobox display if present
                            widget = meta.get("widget") if meta else None
                            if widget is not None:
                                try:
                                    widget.set(BADGE_LEVEL_NAMES[lvl])
                                except Exception:
                                    pass
                        elif meta and isinstance(meta.get("values"), list):
                            # Enumerated field: clamp the raw value to the index range
                            vals = meta.get("values")
                            idx = int(value)
                            if idx < 0:
                                idx = 0
                            elif idx >= len(vals):
                                idx = len(vals) - 1
                            var.set(idx)
                            # Update combobox display
                            widget = meta.get("widget")
                            if widget is not None:
                                try:
                                    widget.set(vals[idx])
                                except Exception:
                                    pass
                        else:
                            # Other categories are shown as their raw integer values
                            var.set(int(value))
                    except Exception:
                        pass

    def _save_all(self) -> None:
        """
        Iterate over all fields and write the current values back to the
        player's record in memory.
        """
        # Iterate similar to load
        any_error = False
        for category, fields in self.field_vars.items():
            for field_name, var in fields.items():
                meta = self.field_meta.get((category, field_name))
                if not meta:
                    continue
                try:
                    offset = meta.get("offset", 0)
                    start_bit = meta.get("start_bit", 0)
                    length = meta.get("length", 0)
                    # Retrieve the value from the UI
                    ui_value = var.get()
                    # Convert rating back to raw bitfield for Attributes,
                    # Durability and Tendencies.  Observations indicate
                    # that ratings are stored with an offset of 10 (i.e., a
                    # rating of 25 corresponds to raw 15 and a rating of 99
                    # corresponds to raw 89).  Therefore we simply
                    # subtract 10 from the rating and clamp the result to
                    # the valid bitfield range.  Other categories are
                    # written as-is.
                    if category in ("Attributes", "Durability"):
                        # Convert the UI rating back into a raw bitfield value.
                        try:
                            rating_val = int(ui_value)
                        except Exception:
                            rating_val = 25
                        value_to_write = convert_rating_to_raw(rating_val, length)
                    elif category == "Tendencies":
                        # Tendencies: convert the 0–100 rating back to raw bitfield
                        try:
                            rating_val = float(ui_value)
                        except Exception:
                            rating_val = 0.0
                        value_to_write = convert_rating_to_tendency_raw(
                            rating_val, length
                        )
                    elif category == "Badges":
                        # Badges: clamp UI value (0–4) to the underlying bitfield
                        try:
                            lvl = int(ui_value)
                        except Exception:
                            lvl = 0
                        if lvl < 0:
                            lvl = 0
                        max_raw = (1 << length) - 1
                        if lvl > max_raw:
                            lvl = max_raw
                        value_to_write = lvl
                    elif meta and isinstance(meta.get("values"), list):
                        # Enumerated field: clamp UI value to the bitfield range
                        try:
                            idx_val = int(ui_value)
                        except Exception:
                            idx_val = 0
                        if idx_val < 0:
                            idx_val = 0
                        max_raw = (1 << length) - 1
                        if idx_val > max_raw:
                            idx_val = max_raw
                        value_to_write = idx_val
                    else:
                        # For other categories, write the raw value directly
                        value_to_write = ui_value
                    if not self.model.set_field_value(
                        self.player.index, offset, start_bit, length, value_to_write
                    ):
                        any_error = True
                except Exception:
                    any_error = True
        if any_error:
            messagebox.showerror("Save Error", "One or more fields could not be saved.")
        else:
            messagebox.showinfo("Save Successful", "All fields saved successfully.")

    def _adjust_category(self, category_name: str, action: str) -> None:
        """
        Adjust all values within a category according to the specified action.

        Actions can be one of: 'min', 'max', 'plus5', 'plus10', 'minus5', 'minus10'.
        For Attributes, Durability and Tendencies categories, values are clamped
        to the 25..99 scale.  For other categories, values are clamped to the
        raw bitfield range (0..(2^length - 1)).
        """
        # Ensure the category exists
        fields = self.field_vars.get(category_name)
        if not fields:
            return
        for field_name, var in fields.items():
            # Retrieve bit length from metadata
            meta = self.field_meta.get((category_name, field_name))
            if not meta:
                continue
            length = meta.get("length", 8)
            # Determine min and max values based on category
            if category_name in ("Attributes", "Durability"):
                # Attributes and Durability: clamp to 25..99
                min_val = 25
                max_val = 99
            elif category_name == "Tendencies":
                # Tendencies: clamp to 0..100
                min_val = 0
                max_val = 100
            else:
                min_val = 0
                max_val = (1 << int(length)) - 1
            current = var.get()
            new_val = current
            if action == "min":
                new_val = min_val
            elif action == "max":
                new_val = max_val
            elif action == "plus5":
                new_val = current + 5
            elif action == "plus10":
                new_val = current + 10
            elif action == "minus5":
                new_val = current - 5
            elif action == "minus10":
                new_val = current - 10
            # Clamp to allowed range
            if new_val < min_val:
                new_val = min_val
            if new_val > max_val:
                new_val = max_val
            var.set(int(new_val))


# ---------------------------------------------------------------------
# Randomizer window
# ---------------------------------------------------------------------
class RandomizerWindow(tk.Toplevel):
    """
    A modal window for randomizing player attributes, tendencies and
    durability values for selected teams.  It presents three tabs
    (Attributes, Tendencies, Durability) where minimum and maximum
    rating bounds can be specified per field, and a fourth tab for
    selecting which teams or pools should be affected.  When the
    "Randomize Selected" button is clicked, random ratings are
    applied to all players on the selected teams.

    Parameters
    ----------
    parent : PlayerEditorApp
        The parent window.  The randomizer window will be centered
        over this window and is modal relative to it.
    model : PlayerDataModel
        The data model used to access players, teams and field
        definitions.
    """

    def __init__(self, parent: "PlayerEditorApp", model: PlayerDataModel) -> None:
        super().__init__(parent)
        self.title("Randomizer")
        self.model = model
        # Dictionaries to hold IntVars for min and max values per field
        self.min_vars: dict[tuple[str, str], tk.IntVar] = {}
        self.max_vars: dict[tuple[str, str], tk.IntVar] = {}
        # BooleanVars for team selection
        self.team_vars: dict[str, tk.BooleanVar] = {}
        # Configure basic appearance
        self.configure(bg="#F5F5F5")
        # Make window modal
        self.transient(parent)
        self.grab_set()
        # Build the user interface
        self._build_ui()
        # Center the window relative to parent
        self.update_idletasks()
        x = parent.winfo_rootx() + (parent.winfo_width() - self.winfo_width()) // 2
        y = parent.winfo_rooty() + (parent.winfo_height() - self.winfo_height()) // 2
        self.geometry(f"+{x}+{y}")

    def _build_ui(self) -> None:
        """Construct the notebook with category and team tabs, plus a close button."""
        notebook = ttk.Notebook(self)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        # Categories to randomize
        categories = ["Attributes", "Tendencies", "Durability"]
        for cat in categories:
            frame = tk.Frame(notebook, bg="#F5F5F5")
            notebook.add(frame, text=cat)
            self._build_category_page(frame, cat)
        # Teams tab
        team_frame = tk.Frame(notebook, bg="#F5F5F5")
        notebook.add(team_frame, text="Teams")
        self._build_team_page(team_frame)
        # Close button at bottom
        tk.Button(
            self,
            text="Close",
            command=self.destroy,
            bg="#B0413E",
            fg="white",
            relief=tk.FLAT,
        ).pack(pady=(0, 10))

    def _build_category_page(self, parent: tk.Frame, category: str) -> None:
        """
        Build a page for a single category (Attributes, Tendencies, Durability).
        Each field has two Spinboxes for specifying minimum and maximum
        ratings.  Default values are 25 and 99.
        """
        canvas = tk.Canvas(parent, bg="#F5F5F5", highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#F5F5F5")
        scroll_frame.bind(
            "<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        # Header row
        tk.Label(
            scroll_frame, text="Field", bg="#F5F5F5", font=("Segoe UI", 10, "bold")
        ).grid(row=0, column=0, sticky=tk.W, padx=(10, 5), pady=2)
        tk.Label(
            scroll_frame, text="Min", bg="#F5F5F5", font=("Segoe UI", 10, "bold")
        ).grid(row=0, column=1, padx=5, pady=2)
        tk.Label(
            scroll_frame, text="Max", bg="#F5F5F5", font=("Segoe UI", 10, "bold")
        ).grid(row=0, column=2, padx=5, pady=2)
        fields = self.model.categories.get(category, [])
        for idx, field in enumerate(fields, start=1):
            name = field.get("name", f"Field {idx}")
            tk.Label(scroll_frame, text=name, bg="#F5F5F5").grid(
                row=idx, column=0, sticky=tk.W, padx=(10, 5), pady=2
            )
            # Set default min/max based on category
            if category in ("Attributes", "Durability"):
                default_min = 25
                default_max = 99
                spin_from = 25
                spin_to = 99
            elif category == "Tendencies":
                default_min = 0
                default_max = 100
                spin_from = 0
                spin_to = 100
            else:
                # Fallback; not expected for randomizer categories
                default_min = 0
                default_max = (1 << int(field.get("length", 8))) - 1
                spin_from = 0
                spin_to = default_max
            min_var = tk.IntVar(value=default_min)
            max_var = tk.IntVar(value=default_max)
            self.min_vars[(category, name)] = min_var
            self.max_vars[(category, name)] = max_var
            tk.Spinbox(
                scroll_frame, from_=spin_from, to=spin_to, textvariable=min_var, width=5
            ).grid(row=idx, column=1, padx=2, pady=2)
            tk.Spinbox(
                scroll_frame, from_=spin_from, to=spin_to, textvariable=max_var, width=5
            ).grid(row=idx, column=2, padx=2, pady=2)

    def _build_team_page(self, parent: tk.Frame) -> None:
        """
        Build the team selection page.  Contains a button to trigger
        randomization and a list of checkboxes for each team/pool.
        """
        btn_randomize = tk.Button(
            parent,
            text="Randomize Selected",
            command=self._randomize_selected,
            bg="#52796F",
            fg="white",
            relief=tk.FLAT,
        )
        btn_randomize.pack(pady=(5, 10))
        canvas = tk.Canvas(parent, bg="#F5F5F5", highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#F5F5F5")
        scroll_frame.bind(
            "<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        # Obtain team names: use get_teams if available, fallback to model.team_list
        team_names = []
        try:
            team_names = self.model.get_teams()
        except Exception:
            team_names = []
        if not team_names:
            team_names = [name for _, name in self.model.team_list]
        # Build checkbuttons for each team
        for idx, team_name in enumerate(team_names):
            var = tk.BooleanVar(value=False)
            self.team_vars[team_name] = var
            chk = tk.Checkbutton(
                scroll_frame, text=team_name, variable=var, bg="#F5F5F5"
            )
            chk.grid(row=idx, column=0, sticky=tk.W, padx=10, pady=2)

    def _randomize_selected(self) -> None:
        """
        Randomize all player values for selected teams using the specified
        bounds.  The ratings are converted from the 25–99 scale into
        raw bitfield values before writing to memory.  After
        randomization, the player list is refreshed and a summary
        message is displayed.
        """
        import tkinter.messagebox as mb

        # Determine which teams are selected
        selected = [team for team, var in self.team_vars.items() if var.get()]
        if not selected:
            mb.showinfo("Randomizer", "No teams selected for randomization.")
            return
        # Categories we randomize
        categories = ["Attributes", "Tendencies", "Durability"]
        updated_players = 0
        for team_name in selected:
            players = self.model.get_players_by_team(team_name)
            if not players:
                continue
            for player in players:
                player_updated = False
                for cat in categories:
                    fields = self.model.categories.get(cat, [])
                    for field in fields:
                        fname = field.get("name")
                        # Check that we have min/max variables for this field
                        key = (cat, fname)
                        if key not in self.min_vars or key not in self.max_vars:
                            continue
                        # Retrieve offset info
                        offset_str = field.get("offset", "0")
                        try:
                            if isinstance(
                                offset_str, str
                            ) and offset_str.lower().startswith("0x"):
                                offset_val = int(offset_str, 16)
                            else:
                                offset_val = int(offset_str)
                        except Exception:
                            offset_val = 0
                        start_bit = int(field.get("startBit", 0))
                        length = int(field.get("length", 8))
                        min_val = self.min_vars[key].get()
                        max_val = self.max_vars[key].get()
                        if min_val > max_val:
                            min_val, max_val = max_val, min_val
                        # Pick a random rating within the user‑specified bounds
                        rating = random.randint(min_val, max_val)
                        # Convert the rating into a raw bitfield value using
                        # the appropriate conversion based on category
                        if cat == "Tendencies":
                            raw_val = convert_rating_to_tendency_raw(rating, length)
                        else:
                            raw_val = convert_rating_to_raw(rating, length)
                        if self.model.set_field_value(
                            player.index, offset_val, start_bit, length, raw_val
                        ):
                            player_updated = True
                if player_updated:
                    updated_players += 1
        # Refresh player list to reflect updated values
        try:
            self.model.refresh_players()
        except Exception:
            pass
        mb.showinfo(
            "Randomizer", f"Randomization complete. {updated_players} players updated."
        )


# ---------------------------------------------------------------------
# Team Shuffle window
# ---------------------------------------------------------------------
class TeamShuffleWindow(tk.Toplevel):
    """
    A modal window that lets the user select one or more teams and then
    shuffle the players among those teams.  The shuffle maintains the
    original roster sizes (players per team) and will not proceed if
    any selected team has more than 15 players.  After shuffling, the
    team pointers in each player record are updated to reflect their
    new teams and the player list is refreshed.

    Parameters
    ----------
    parent : PlayerEditorApp
        The parent window; the shuffle window will be modal over this.
    model : PlayerDataModel
        The data model used to access players and memory addresses.
    """

    def __init__(self, parent: "PlayerEditorApp", model: PlayerDataModel) -> None:
        super().__init__(parent)
        self.title("Team Shuffle")
        self.model = model
        self.team_vars: dict[str, tk.BooleanVar] = {}
        # Modal setup
        self.configure(bg="#F5F5F5")
        self.transient(parent)
        self.grab_set()
        # Build UI
        self._build_ui()
        # Center relative to parent
        self.update_idletasks()
        x = parent.winfo_rootx() + (parent.winfo_width() - self.winfo_width()) // 2
        y = parent.winfo_rooty() + (parent.winfo_height() - self.winfo_height()) // 2
        self.geometry(f"+{x}+{y}")

    def _build_ui(self) -> None:
        """Construct the UI for selecting teams and initiating the shuffle."""
        # Instruction label
        tk.Label(
            self,
            text="Select teams to shuffle players among them:",
            bg="#F5F5F5",
            font=("Segoe UI", 11),
        ).pack(pady=(10, 5))
        # Scrollable list of teams
        frame = tk.Frame(self, bg="#F5F5F5")
        frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        canvas = tk.Canvas(frame, bg="#F5F5F5", highlightthickness=0)
        scrollbar = tk.Scrollbar(frame, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#F5F5F5")
        scroll_frame.bind(
            "<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        # Fetch team names: use get_teams or team_list fallback
        team_names = []
        try:
            team_names = self.model.get_teams()
        except Exception:
            team_names = []
        if not team_names:
            team_names = [name for _, name in self.model.team_list]
        # Build checkboxes
        for idx, team_name in enumerate(team_names):
            var = tk.BooleanVar(value=False)
            self.team_vars[team_name] = var
            chk = tk.Checkbutton(
                scroll_frame, text=team_name, variable=var, bg="#F5F5F5"
            )
            chk.grid(row=idx, column=0, sticky=tk.W, padx=10, pady=2)
        # Shuffle button
        btn = tk.Button(
            self,
            text="Shuffle Selected",
            command=self._shuffle_selected,
            bg="#52796F",
            fg="white",
            relief=tk.FLAT,
        )
        btn.pack(pady=(0, 10))
        # Close button
        tk.Button(
            self,
            text="Close",
            command=self.destroy,
            bg="#B0413E",
            fg="white",
            relief=tk.FLAT,
        ).pack(pady=(0, 10))

    def _shuffle_selected(self) -> None:
        """
        Shuffle players across the selected teams.

        The updated shuffling logic first dumps all players from the
        selected teams into the Free Agents pool, then randomly
        assigns exactly 15 players back to each selected team.  Any
        leftover players remain in Free Agents.  Unlike the old
        implementation, this function works whether or not team
        pointers are available and does not enforce a per‑team roster
        maximum prior to shuffling.
        """
        import tkinter.messagebox as mb
        import random as _random

        selected = [team for team, var in self.team_vars.items() if var.get()]
        if not selected:
            mb.showinfo("Shuffle Teams", "No teams selected.")
            return
        # Gather all players from the selected teams
        players_to_pool: list[Player] = []
        for team in selected:
            plist = self.model.get_players_by_team(team)
            if plist:
                players_to_pool.extend(plist)
        if not players_to_pool:
            mb.showinfo("Shuffle Teams", "No players to shuffle.")
            return
        # Determine whether we are in live memory mode.  Shuffling in
        # live memory writes directly to the game process; fallback mode
        # simply updates the in‑memory roster representation.
        live_mode = not self.model.fallback_players
        total_assigned = 0
        if live_mode:
            # Resolve base pointers
            team_base = self.model._resolve_team_base_ptr()
            player_base = self.model._resolve_player_table_base()
            if team_base is None or player_base is None:
                mb.showerror(
                    "Shuffle Teams", "Failed to resolve team or player table pointers."
                )
                return
            # Find the Free Agents team pointer
            free_ptr = None
            for idx, name in self.model.team_list:
                if name and "free" in name.lower():
                    free_ptr = team_base + idx * TEAM_RECORD_SIZE
                    break
            if free_ptr is None:
                mb.showerror("Shuffle Teams", "Free Agents team could not be located.")
                return
            # Build mapping of selected team name -> team pointer
            team_ptrs: dict[str, int] = {}
            for idx, name in self.model.team_list:
                if name in selected:
                    team_ptrs[name] = team_base + idx * TEAM_RECORD_SIZE
            # Dump all selected players to Free Agents
            for p in players_to_pool:
                try:
                    p_addr = player_base + p.index * PLAYER_STRIDE
                    self.model.mem.write_bytes(
                        p_addr + OFF_TEAM_PTR, struct.pack("<Q", free_ptr)
                    )
                    p.team = "Free Agents"
                except Exception:
                    # Ignore write failures for individual players
                    pass
            # Shuffle the pooled players
            _random.shuffle(players_to_pool)
            pos = 0
            # Assign up to 15 players back to each selected team
            for team in selected:
                ptr = team_ptrs.get(team)
                if ptr is None:
                    continue
                for i in range(15):
                    if pos >= len(players_to_pool):
                        break
                    player = players_to_pool[pos]
                    pos += 1
                    try:
                        p_addr = player_base + player.index * PLAYER_STRIDE
                        self.model.mem.write_bytes(
                            p_addr + OFF_TEAM_PTR, struct.pack("<Q", ptr)
                        )
                        player.team = team
                        total_assigned += 1
                    except Exception:
                        pass
            # Refresh the player list so the UI reflects new assignments
            try:
                self.model.refresh_players()
            except Exception:
                pass
        else:
            # Offline mode: update the player objects only
            # Dump all selected players to Free Agents
            for p in players_to_pool:
                p.team = "Free Agents"
            # Shuffle the pool and assign 15 players back to each team
            _random.shuffle(players_to_pool)
            pos = 0
            for team in selected:
                for i in range(15):
                    if pos >= len(players_to_pool):
                        break
                    p = players_to_pool[pos]
                    pos += 1
                    p.team = team
                    total_assigned += 1
            # Rebuild the name index map after shuffling
            self.model._build_name_index_map()
        # Report summary
        mb.showinfo(
            "Shuffle Teams",
            f"Shuffle complete. {total_assigned} players reassigned. Remaining players are Free Agents.",
        )


# ---------------------------------------------------------------------
# Batch Edit window
# ---------------------------------------------------------------------
class BatchEditWindow(tk.Toplevel):
    """
    A modal window for applying a single value to a field across many players.
    Users select one or more teams, choose a category, select a field in
    that category and then specify a new value.  When the Apply button is
    clicked, the chosen value is written to the selected field for every
    player on the selected teams via PlayerDataModel.set_field_value.

    Only live memory editing is supported; if the game is not running or the
    player table cannot be resolved, no changes will be made.  The editor
    supports both numeric fields and enumerated fields (via combobox).

    Parameters
    ----------
    parent : PlayerEditorApp
        The parent window; the batch edit window will be modal over it.
    model : PlayerDataModel
        The data model used to access players, teams and field definitions.
    """

    def __init__(self, parent: "PlayerEditorApp", model: PlayerDataModel) -> None:
        super().__init__(parent)
        self.title("Batch Edit")
        self.model = model
        # Mapping of team name to selection variable
        self.team_vars: dict[str, tk.BooleanVar] = {}
        # Variables for selected category and field
        self.category_var = tk.StringVar()
        self.field_var = tk.StringVar()
        # The input widget and associated variable for the value
        self.value_widget: tk.Widget | None = None
        self.value_var: tk.Variable | None = None
        # Configure window appearance and modality
        self.configure(bg="#F5F5F5")
        self.transient(parent)
        self.grab_set()
        # Build the UI
        self._build_ui()
        # Center relative to parent
        self.update_idletasks()
        x = parent.winfo_rootx() + (parent.winfo_width() - self.winfo_width()) // 2
        y = parent.winfo_rooty() + (parent.winfo_height() - self.winfo_height()) // 2
        self.geometry(f"+{x}+{y}")

    def _build_ui(self) -> None:
        """Construct the user interface for selecting teams, category, field and value."""
        # Instruction label
        tk.Label(
            self,
            text="Select teams, choose a field and enter a value:",
            bg="#F5F5F5",
            font=("Segoe UI", 11),
        ).pack(pady=(10, 5))
        # Selection frame for category and field
        sel_frame = tk.Frame(self, bg="#F5F5F5")
        sel_frame.pack(fill=tk.X, padx=10)
        tk.Label(sel_frame, text="Category:", bg="#F5F5F5").grid(
            row=0, column=0, sticky=tk.W, padx=(0, 5), pady=2
        )
        categories = list(self.model.categories.keys())
        self.category_combo = ttk.Combobox(
            sel_frame,
            textvariable=self.category_var,
            state="readonly",
            values=categories,
        )
        self.category_combo.grid(row=0, column=1, sticky=tk.W, pady=2)
        self.category_combo.bind("<<ComboboxSelected>>", self._on_category_selected)
        tk.Label(sel_frame, text="Field:", bg="#F5F5F5").grid(
            row=1, column=0, sticky=tk.W, padx=(0, 5), pady=2
        )
        self.field_combo = ttk.Combobox(
            sel_frame, textvariable=self.field_var, state="readonly", values=[]
        )
        self.field_combo.grid(row=1, column=1, sticky=tk.W, pady=2)
        self.field_combo.bind("<<ComboboxSelected>>", self._on_field_selected)
        # Input frame for value widget
        self.input_frame = tk.Frame(self, bg="#F5F5F5")
        self.input_frame.pack(fill=tk.X, padx=10, pady=(5, 5))
        # Team selection area
        teams_frame = tk.Frame(self, bg="#F5F5F5")
        teams_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        canvas = tk.Canvas(teams_frame, bg="#F5F5F5", highlightthickness=0)
        scrollbar = tk.Scrollbar(teams_frame, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#F5F5F5")
        scroll_frame.bind(
            "<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        # Populate team checkboxes
        try:
            team_names = self.model.get_teams()
        except Exception:
            team_names = []
        if not team_names:
            team_names = [name for _, name in self.model.team_list]
        for idx, name in enumerate(team_names):
            var = tk.BooleanVar(value=False)
            self.team_vars[name] = var
            chk = tk.Checkbutton(scroll_frame, text=name, variable=var, bg="#F5F5F5")
            chk.grid(row=idx, column=0, sticky=tk.W, padx=5, pady=2)
        # Buttons for apply and close
        btn_frame = tk.Frame(self, bg="#F5F5F5")
        btn_frame.pack(fill=tk.X, padx=10, pady=(0, 10))
        apply_btn = tk.Button(
            btn_frame,
            text="Apply",
            command=self._apply_changes,
            bg="#52796F",
            fg="white",
            relief=tk.FLAT,
        )
        apply_btn.pack(side=tk.LEFT, padx=(0, 5))
        close_btn = tk.Button(
            btn_frame,
            text="Close",
            command=self.destroy,
            bg="#B0413E",
            fg="white",
            relief=tk.FLAT,
        )
        close_btn.pack(side=tk.RIGHT)

    def _on_category_selected(self, _event: tk.Event | None = None) -> None:
        """Update the field dropdown when a new category is selected."""
        category = self.category_var.get()
        self.field_var.set("")
        # Remove any existing input widget
        if self.value_widget is not None:
            self.value_widget.destroy()
            self.value_widget = None
            self.value_var = None
        # Populate field names for this category
        fields = self.model.categories.get(category, [])
        names = [f.get("name", "") for f in fields]
        self.field_combo.config(values=names)
        self.field_combo.set("")

    def _on_field_selected(self, _event: tk.Event | None = None) -> None:
        """Create the appropriate input control for the selected field."""
        category = self.category_var.get()
        field_name = self.field_var.get()
        # Remove existing value widget
        if self.value_widget is not None:
            self.value_widget.destroy()
            self.value_widget = None
            self.value_var = None
        # Find field definition
        field_def = None
        for fd in self.model.categories.get(category, []):
            if fd.get("name") == field_name:
                field_def = fd
                break
        if not field_def:
            return
        values_list = field_def.get("values")
        length = int(field_def.get("length", 0))
        if values_list:
            # Enumerated field: use combobox
            self.value_var = tk.IntVar()
            disp_vals = list(values_list)
            combo = ttk.Combobox(
                self.input_frame, state="readonly", values=disp_vals, width=25
            )
            combo.pack(fill=tk.X, pady=(0, 5))
            self.value_widget = combo
            if disp_vals:
                combo.current(0)
        else:
            # Numeric field: use spinbox
            if category in ("Attributes", "Tendencies", "Durability"):
                min_val = 25
                max_val = 99
            else:
                min_val = 0
                max_val = (1 << length) - 1 if length else 255
            self.value_var = tk.IntVar(value=min_val)
            spin = tk.Spinbox(
                self.input_frame,
                from_=min_val,
                to=max_val,
                textvariable=self.value_var,
                width=10,
                increment=1,
                justify=tk.LEFT,
            )
            spin.pack(fill=tk.X, pady=(0, 5))
            self.value_widget = spin

    def _apply_changes(self) -> None:
        """Write the specified value to the selected field for all players on the selected teams."""
        import tkinter.messagebox as mb

        category = self.category_var.get()
        field_name = self.field_var.get()
        if not category or not field_name:
            mb.showinfo("Batch Edit", "Please select a category and field.")
            return
        # Collect selected teams
        selected_teams = [name for name, var in self.team_vars.items() if var.get()]
        if not selected_teams:
            mb.showinfo("Batch Edit", "Please select one or more teams.")
            return
        # Find the field definition
        field_def = None
        for fd in self.model.categories.get(category, []):
            if fd.get("name") == field_name:
                field_def = fd
                break
        if not field_def:
            mb.showerror("Batch Edit", "Field definition not found.")
            return
        # Parse offset and bit positions
        try:
            offset_val = int(field_def.get("offset"), 0)
        except Exception:
            mb.showerror("Batch Edit", f"Invalid offset for field '{field_name}'.")
            return
        start_bit = int(field_def.get("startBit", 0))
        length = int(field_def.get("length", 0))
        values_list = field_def.get("values")
        # Determine value to write
        if values_list:
            # Enumerated: index corresponds to stored value
            combo = self.value_widget  # type: ignore
            if hasattr(combo, "current"):
                sel_idx = combo.current()
            else:
                sel_idx = 0
            if sel_idx < 0:
                mb.showinfo("Batch Edit", "Please select a value.")
                return
            value_to_write = sel_idx
            max_val = (1 << length) - 1 if length else len(values_list) - 1
            if value_to_write > max_val:
                value_to_write = max_val
        else:
            # Numeric value
            try:
                numeric_val = float(self.value_var.get()) if self.value_var else 0
            except Exception:
                numeric_val = 0
            if category in ("Attributes", "Durability"):
                value_to_write = convert_rating_to_raw(numeric_val, length)
            elif category == "Tendencies":
                value_to_write = convert_rating_to_tendency_raw(numeric_val, length)
            else:
                max_val = (1 << length) - 1 if length else 255
                value_to_write = int(max(0, min(max_val, numeric_val)))
        # Verify connection to the game
        if not self.model.mem.hproc:
            mb.showinfo("Batch Edit", "NBA 2K25 is not running. Cannot apply changes.")
            return
        # Apply changes for each player on each selected team
        total_changed = 0
        for team_name in selected_teams:
            players = self.model.get_players_by_team(team_name)
            for player in players:
                success = self.model.set_field_value(
                    player.index, offset_val, start_bit, length, value_to_write
                )
                if success:
                    total_changed += 1
        mb.showinfo("Batch Edit", f"Applied value to {total_changed} players.")
        # Refresh players to update the UI
        try:
            self.model.refresh_players()
        except Exception:
            pass
        # Close the window
        self.destroy()


# -----------------------------------------------------------------------------
# Category selection dialog for COY imports
#
# When invoking the COY import from the side bar, the user can choose which
# categories (Attributes, Tendencies, Durability) they wish to import.  This
# dialog presents a list of checkboxes and returns the selected categories
# when the user clicks OK.  If the dialog is cancelled or no categories are
# selected, ``selected`` is set to None.


class CategorySelectionDialog(tk.Toplevel):
    """
    Simple modal dialog that allows the user to select one or more categories
    for the COY import.  Categories are presented as checkboxes.  The
    selected categories are stored in the ``selected`` attribute after
    ``OK`` is pressed; if cancelled, ``selected`` is ``None``.
    """

    def __init__(self, parent: tk.Misc, categories: list[str]) -> None:
        super().__init__(parent)
        self.title("Select categories to import")
        self.resizable(False, False)
        # Ensure the dialog appears above its parent
        self.transient(parent)
        self.grab_set()
        # Internal storage for selected categories; None until closed
        self.selected: list[str] | None = []
        # Create a label
        tk.Label(self, text="Import the following categories:").pack(
            padx=10, pady=(10, 5)
        )
        # Create a frame to hold the checkboxes
        frame = tk.Frame(self)
        frame.pack(padx=10, pady=5)
        # Dictionary mapping category names to BooleanVars
        self.var_map: dict[str, tk.BooleanVar] = {}
        for cat in categories:
            var = tk.BooleanVar(value=True)
            chk = tk.Checkbutton(frame, text=cat, variable=var)
            chk.pack(anchor=tk.W)
            self.var_map[cat] = var
        # OK and Cancel buttons
        btn_frame = tk.Frame(self)
        btn_frame.pack(pady=(5, 10))
        tk.Button(btn_frame, text="OK", width=10, command=self._on_ok).pack(
            side=tk.LEFT, padx=5
        )
        tk.Button(btn_frame, text="Cancel", width=10, command=self._on_cancel).pack(
            side=tk.LEFT, padx=5
        )

    def _on_ok(self) -> None:
        """Gather selected categories and close the dialog."""
        selected: list[str] = []
        for cat, var in self.var_map.items():
            try:
                if var.get():
                    selected.append(cat)
            except Exception:
                pass
        # If no categories selected, set None to indicate cancel
        if not selected:
            self.selected = None
        else:
            self.selected = selected
        self.destroy()

    def _on_cancel(self) -> None:
        """Cancel the dialog without selecting any categories."""
        self.selected = None
        self.destroy()


def main() -> None:
    # Only run on Windows; bail early otherwise
    if sys.platform != "win32":
        messagebox.showerror(
            "Unsupported platform", "This application can only run on Windows."
        )
        return
    mem = GameMemory(MODULE_NAME)
    model = PlayerDataModel(mem, max_players=MAX_PLAYERS)
    app = PlayerEditorApp(model)
    app.mainloop()


if __name__ == "__main__":
    main()
