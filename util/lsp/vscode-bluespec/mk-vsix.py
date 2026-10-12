#!/usr/bin/env python3
"""Build a VS Code extension package (.vsix) without requiring vsce or Node >=20.

A .vsix file is a ZIP archive with the following layout:
  [Content_Types].xml
  extension.vsixmanifest
  extension/           <- all extension source files

Usage:
  python3 mk-vsix.py <extension-dir> <output.vsix>
"""
import json
import os
import sys
import zipfile
from pathlib import Path

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

CONTENT_TYPES_XML = """\
<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
  <Default Extension=".json"         ContentType="application/json"/>
  <Default Extension=".js"           ContentType="text/javascript"/>
  <Default Extension=".md"           ContentType="text/markdown"/>
  <Default Extension=".png"          ContentType="image/png"/>
  <Default Extension=".vsixmanifest" ContentType="text/xml"/>
  <Default Extension=".txt"          ContentType="text/plain"/>
  <Default Extension=".map"          ContentType="application/json"/>
  <Default Extension=".ts"           ContentType="text/x-typescript"/>
</Types>
"""

VSIX_MANIFEST_TEMPLATE = """\
<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0"
    xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011"
    xmlns:d="http://schemas.microsoft.com/developer/vsx-schema-design/2011">
  <Metadata>
    <Identity Language="en-US"
              Id="{ext_id}"
              Version="{version}"
              Publisher="{publisher}"/>
    <DisplayName>{display_name}</DisplayName>
    <Description xml:space="preserve">{description}</Description>
    <Categories>{categories}</Categories>
    <Tags></Tags>
    <GalleryFlags></GalleryFlags>
    <Properties>
      <Property Id="Microsoft.VisualStudio.Code.Engine" Value="{engine}"/>
    </Properties>
  </Metadata>
  <Installation>
    <InstallationTarget Id="Microsoft.VisualStudio.Code"/>
  </Installation>
  <Dependencies/>
  <Assets>
    <Asset Type="Microsoft.VisualStudio.Code.Manifest"
           Path="extension/package.json"
           Addressable="true"/>
  </Assets>
</PackageManifest>
"""

# Directories / patterns to exclude from the extension zip
EXCLUDE_DIRS  = {'.git', '.vscode', '__pycache__', '.DS_Store'}
EXCLUDE_FILES = {'.vscodeignore', '.gitignore', 'mk-vsix.py', 'setup.sh'}
EXCLUDE_EXTS  = {'.vsix'}


def should_exclude(rel: Path) -> bool:
    parts = rel.parts
    # Skip hidden top-level dirs/files except node_modules
    if parts[0].startswith('.') and parts[0] != '.':
        return True
    if parts[0] in EXCLUDE_DIRS:
        return True
    if len(parts) == 1 and parts[0] in EXCLUDE_FILES:
        return True
    if len(parts) == 1 and rel.suffix in EXCLUDE_EXTS:
        return True
    return False


def build_vsix(ext_dir: Path, out_path: Path) -> None:
    pkg_path = ext_dir / 'package.json'
    if not pkg_path.exists():
        sys.exit(f"ERROR: {pkg_path} not found")

    pkg = json.loads(pkg_path.read_text())
    ext_id      = pkg['name']
    version     = pkg['version']
    publisher   = pkg['publisher']
    display     = pkg.get('displayName', ext_id)
    description = pkg.get('description', '')
    categories  = ','.join(pkg.get('categories', []))
    engine      = pkg.get('engines', {}).get('vscode', '*')

    manifest = VSIX_MANIFEST_TEMPLATE.format(
        ext_id=ext_id,
        version=version,
        publisher=publisher,
        display_name=display,
        description=description,
        categories=categories,
        engine=engine,
    )

    print(f"  Publisher : {publisher}")
    print(f"  ID        : {ext_id}")
    print(f"  Version   : {version}")

    file_count = 0
    with zipfile.ZipFile(out_path, 'w', compression=zipfile.ZIP_DEFLATED) as zf:
        # Required top-level metadata
        zf.writestr('[Content_Types].xml', CONTENT_TYPES_XML)
        zf.writestr('extension.vsixmanifest', manifest)

        # Walk the extension directory
        for root, dirs, files in os.walk(ext_dir):
            # Prune excluded dirs in-place
            dirs[:] = [d for d in sorted(dirs) if d not in EXCLUDE_DIRS and not d.startswith('.')]

            for fname in sorted(files):
                abs_path = Path(root) / fname
                rel      = abs_path.relative_to(ext_dir)
                if should_exclude(rel):
                    continue
                arc_name = f'extension/{rel}'
                zf.write(abs_path, arc_name)
                file_count += 1

    print(f"  Files     : {file_count}")
    print(f"  Output    : {out_path}  ({out_path.stat().st_size:,} bytes)")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.exit(f"Usage: {sys.argv[0]} <extension-dir> <output.vsix>")

    ext_dir  = Path(sys.argv[1]).resolve()
    out_path = Path(sys.argv[2])

    if out_path.exists():
        out_path.unlink()

    build_vsix(ext_dir, out_path)
