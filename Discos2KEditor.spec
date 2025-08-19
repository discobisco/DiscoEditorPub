# Discos2KEditor.spec — bundles all loose text files + folders
block_cipher = None

a = Analysis(
    ['2k25_player_patcher_gui_patched_homepage.py'],
    pathex=[],
    binaries=[],
    datas=[
        # Assets
        ('homepage_logo.png', '.'),
        ('discos2k.ico', '.'),
        ('version_info.txt', '.'),
        ('Offsets.txt', '.'),

        # Loose text files in root
        ('2K25 Edit Player (10.18.24).txt', '.'),
        ('Player Data Patch 4.txt', '.'),
        ('2K25 Team Data (10.18.24).txt', '.'),
        ('2K25 Stadium Data (10.18.24).txt', '.'),
        ('2K25 Player Stats Data (10.18.24).txt', '.'),
        ('2K25 Player Data (10.18.24).txt', '.'),

    ],
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    win_no_prefer_redirects=False,
    win_private_assemblies=False,
    cipher=block_cipher,
    noarchive=False,
)
pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)

exe = EXE(
    pyz,
    a.scripts,
    [],
    exclude_binaries=True,
    name='Discos2KEditor',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    icon='discos2k.ico',
    version='version_info.txt',
)
coll = COLLECT(
    exe, a.binaries, a.zipfiles, a.datas,
    strip=False, upx=True, upx_exclude=[],
    name='Discos2KEditor'
)
