"""
Offset Reader and Restructurer
==============================

This module provides a simple way to load the 2K25 offsets file
(`Offsets.txt` or any compatible JSON) and restructure it into
a more convenient format.  The offsets file supplied with the
project contains a ``Base`` section and a number of categories
(``Body``, ``Vitals``, ``Attributes``, etc.), each with a list of
field dictionaries.  Each field has a ``name``, an ``offset``
(hex string), a ``length`` (number of bits), and optionally a
``startBit``.  While this structure mirrors the cheat engine
tables, it can be cumbersome to work with directly.

To simplify lookups, this script reorganizes each category into
a dictionary keyed by the offset.  For example, rather than
iterating through a list of fields to find the one at offset
``0x39B``, the restructured version exposes ``data["Attributes"]["0x39B"]``.
Bit fields that share the same byte offset (but have different
``startBit`` values) are stored as lists under that key.

Usage
-----

You can run this script directly to restructure an offsets file and
write the result to ``offsets_dynamic.json``:

```
python offsets_reader.py --input Offsets.txt --output offsets_dynamic.json
```

Alternatively, import the ``load_offsets`` and ``restructure`` functions
from this module in your own code to build the structure at runtime.
"""

from __future__ import annotations

import json
import argparse
from pathlib import Path
from typing import Any, Dict, List, Union


def load_offsets(path: Union[str, Path]) -> Dict[str, Any]:
    """Load an offsets JSON file.

    This helper simply reads the file and returns the parsed
    JSON as a Python dictionary.  It raises an exception if
    the file does not exist or cannot be parsed.

    Parameters
    ----------
    path : Union[str, Path]
        Path to the offsets file.  The file must contain valid JSON.

    Returns
    -------
    dict
        Parsed offsets data.
    """
    with open(path, "r", encoding="utf-8") as f:
        content = f.read().strip()
        # Attempt direct JSON parsing first.  Some offsets files are
        # missing the outer braces; if so, wrap the content.  If the
        # parser still fails, fall back to a manual parser that
        # extracts each top-level key individually.
        json_str = content
        if json_str and not json_str.startswith("{"):
            json_str = "{" + json_str + "}"
        try:
            return json.loads(json_str)
        except json.JSONDecodeError:
            # Fallback: manually parse the top-level keys.  This
            # implementation scans for quoted keys and parses their
            # corresponding values (objects or arrays) using the JSON
            # decoder.  It ignores unknown syntax and is robust to
            # trailing commas or missing braces at the top level.
            return _manual_parse_offsets(content)


def _manual_parse_offsets(content: str) -> Dict[str, Any]:
    """Manually parse an offsets file lacking a top-level wrapper.

    This parser scans for quoted keys at the start of a line and
    extracts the following JSON object or array using the standard
    decoder.  It is tolerant of leading whitespace and commas
    between entries.  Unknown syntax outside of recognized
    categories is ignored.

    Parameters
    ----------
    content : str
        Raw content of the offsets file (e.g. from ``Offsets.txt``).

    Returns
    -------
    dict
        A dictionary mapping category names to their values.
    """
    data: Dict[str, Any] = {}
    i = 0
    n = len(content)
    while i < n:
        # Skip whitespace and commas
        while i < n and content[i] in " \t\r\n,":
            i += 1
        if i >= n or content[i] != '"':
            break
        # Find the closing quote for the key
        key_start = i + 1
        key_end = content.find('"', key_start)
        if key_end == -1:
            break
        key = content[key_start:key_end]
        i = key_end + 1
        # Skip whitespace and colon
        while i < n and content[i] not in '{[':
            i += 1
        if i >= n:
            break
        # Determine the opening brace or bracket
        if content[i] == '{':
            # Parse an object
            start = i
            brace = 0
            while i < n:
                if content[i] == '{':
                    brace += 1
                elif content[i] == '}':
                    brace -= 1
                    if brace == 0:
                        i += 1
                        break
                i += 1
            obj_str = content[start:i]
            try:
                obj = json.loads(obj_str)
                data[key] = obj
            except Exception:
                # Skip invalid object
                pass
        elif content[i] == '[':
            # Parse an array
            start = i
            bracket = 0
            while i < n:
                if content[i] == '[':
                    bracket += 1
                elif content[i] == ']':
                    bracket -= 1
                    if bracket == 0:
                        i += 1
                        break
                i += 1
            arr_str = content[start:i]
            try:
                arr = json.loads(arr_str)
                data[key] = arr
            except Exception:
                # Skip invalid array
                pass
        else:
            # Unknown structure; skip until next comma or newline
            while i < n and content[i] not in ',\n':
                i += 1
            i += 1
    return data


def restructure(offsets: Dict[str, Any]) -> Dict[str, Any]:
    """Reorganize the offsets dictionary into a nested mapping.

    The input dictionary is expected to follow the format used by the
    "Offsets.txt" file: a top-level "Base" key and one or more
    category keys whose values are lists of field definitions.  This
    function preserves the "Base" section unchanged but replaces
    each category list with a dictionary keyed by the field offset.
    Fields sharing the same offset (but different bit positions) are
    grouped into a list at that key.

    Example output structure::

        {
            "Base": { ... },
            "Attributes": {
                "0x39B": [
                    {"name": "Pass Accuracy", "length": 8, "startBit": 0},
                    {"name": "Ball Control",  "length": 8, "startBit": 0}
                ],
                "0x39C": [ { ... }, { ... } ],
                ...
            },
            ...
        }

    Parameters
    ----------
    offsets : Dict[str, Any]
        The original offsets dictionary (parsed from JSON).

    Returns
    -------
    Dict[str, Any]
        The reorganized offsets dictionary.
    """
    restructured: Dict[str, Any] = {}
    for key, value in offsets.items():
        if key.lower() == "base":
            # Preserve the Base section as-is
            restructured[key] = value
        elif isinstance(value, list):
            cat_map: Dict[str, List[Dict[str, Any]]] = {}
            for field in value:
                # Normalize the offset and startBit
                offset_hex = field.get("offset")
                if not offset_hex:
                    continue
                # Normalize startBit to 0 if missing
                start_bit = field.get("startBit", 0)
                length = field.get("length")
                name = field.get("name")
                # Build a simplified field entry without the original key names
                entry = {
                    "name": name,
                    "length": length,
                    "startBit": start_bit,
                }
                # Insert into the category map; group by offset
                entries = cat_map.setdefault(offset_hex, [])
                entries.append(entry)
            restructured[key] = cat_map
        else:
            # Unknown category type; copy as-is
            restructured[key] = value
    return restructured


def main(argv: List[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Reconstruct and reorganize 2K25 offsets")
    parser.add_argument(
        "--input",
        type=str,
        default="Offsets.txt",
        help="Path to the original offsets JSON file (e.g. Offsets.txt)",
    )
    parser.add_argument(
        "--output",
        type=str,
        default="offsets_dynamic.json",
        help="Path to write the restructured offsets file",
    )
    args = parser.parse_args(argv)
    offsets = load_offsets(args.input)
    restructured = restructure(offsets)
    # Write the reorganized structure to the output file
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(restructured, f, indent=2)
    print(f"Wrote restructured offsets to {args.output}")


if __name__ == "__main__":
    main()