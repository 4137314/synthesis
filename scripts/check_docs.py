#!/usr/bin/env python3
"""Require generated public API pages and the search index before publication."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docbuild/.lake/build/api/doc"


def main() -> None:
    required = ["index.html", "Synthesis.html", "Synthesis/Domains.html", "Synthesis/Bridges.html", "Synthesis/IR.html", "Synthesis/Design.html",
                "Synthesis/Semantics.html", "Synthesis/Frontend.html", "Synthesis/Interop.html"]
    for folder in ["Core", "Logic", "Physics", "Systems", "IR", "Semantics", "Design", "Interop", "Frontend", "Domains", "Bridges"]:
        for source in (ROOT / "Synthesis" / folder).rglob("*.lean"):
            required.append(str(source.relative_to(ROOT).with_suffix(".html")))
    missing = [name for name in required if not (OUTPUT / name).is_file()]
    if missing:
        raise SystemExit("Missing API documentation: " + ", ".join(missing))
    # An empty static site must never be treated as a successful documentation build.
    index = OUTPUT / "declarations/declaration-data.bmp"
    if not index.is_file():
        raise SystemExit("Missing declaration search data")
    declarations = json.loads(index.read_text(encoding="utf-8")).get("declarations", {})
    for name in ["Synthesis.IR.Module", "Synthesis.IR.Extension", "Synthesis.IR.Typed",
                 "Synthesis.Design.Model", "Synthesis.Design.System", "Synthesis.Frontend.compileSystem",
                 "Synthesis.Interop.Exporter", "Synthesis.IR.EntityRef", "Synthesis.IR.Module.walk",
                 "Synthesis.IR.Module.encode", "Synthesis.IR.Extension.combineMany",
                 "Synthesis.Interop.TranslationValidator", "Synthesis.Design.CertifiedRealization",
                 "Synthesis.Frontend.compile", "Synthesis.Domains.RealElectronics.passive",
                 "Synthesis.Bridges.Electrothermal.heater_verified"]:
        if name not in declarations:
            raise SystemExit(f"Missing searchable public declaration: {name}")
    for name in ("Synthesis.IR.Technology", "Synthesis.IR.Component", "Synthesis.IR.Domain",
                 "Synthesis.IR.PortType", "Synthesis.Parameter"):
        if name in declarations:
            raise SystemExit(f"Obsolete schema-2 declaration remains searchable: {name}")
    print(f"documentation: {len(required)} public API pages and search data verified")


if __name__ == "__main__":
    main()
