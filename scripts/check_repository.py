#!/usr/bin/env python3
"""Check module coverage, dependency boundaries, proof policy, and source hygiene."""
from pathlib import Path
import re
import json
import sys

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = {"sorry", "admit", "axiom", "unsafe", "native_decide"}


def lean_code(source: str) -> str:
    """Mask strings and nested comments, retaining positions for useful diagnostics."""
    result = list(source)
    depth = 0
    quoted = False
    i = 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                result[i:i + 2] = "  "
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                result[i:i + 2] = "  "
                i += 2
            else:
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif quoted:
            if source[i] == "\\" and i + 1 < len(source):
                result[i:i + 2] = "  "
                i += 2
            else:
                quoted = source[i] != '"'
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            result[i:i + 2] = "  "
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            result[i:end] = " " * (end - i)
            i = end
        elif source[i] == '"':
            result[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    return "".join(result)


def main() -> int:
    sources = [ROOT / "Synthesis.lean", *sorted((ROOT / "Synthesis").rglob("*.lean")),
               *sorted((ROOT / "Tests").rglob("*.lean"))]
    modules = {str(p.relative_to(ROOT).with_suffix("")).replace("/", "."): p for p in sources}
    graph: dict[str, list[str]] = {}
    errors: list[str] = []
    manifests = [json.loads((ROOT / path).read_text()) for path in
                 ["lake-manifest.json", "docbuild/lake-manifest.json"]]
    pins = [{p["name"]: p["rev"] for p in manifest["packages"] if p["type"] == "git"}
            for manifest in manifests]
    for package, revision in pins[0].items():
        if pins[1].get(package) != revision:
            errors.append(f"{package}: root and documentation dependency pins differ")
    for closure in pins:
        for package, revision in closure.items():
            if not re.fullmatch(r"[0-9a-f]{40}", revision):
                errors.append(f"{package}: dependency is not pinned to a full commit")
    if (ROOT / "lean-toolchain").read_text().strip() != (ROOT / "docbuild/lean-toolchain").read_text().strip():
        errors.append("root and documentation Lean toolchains differ")
    for module, path in modules.items():
        text = path.read_text(encoding="utf-8")
        code = lean_code(text)
        for token in re.finditer(rf"\b(?:{'|'.join(sorted(FORBIDDEN))})\b", code):
            line = code.count("\n", 0, token.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: prohibited token {token[0]}")
        imports = re.findall(r"^import\s+([\w.]+)\s*$", code, re.MULTILINE)
        graph[module] = []
        for dependency in imports:
            if dependency == "Synthesis" or dependency.startswith(("Synthesis.", "Tests.")):
                if dependency not in modules:
                    errors.append(f"{module}: missing project module {dependency}")
                else:
                    graph[module].append(dependency)
            if module == "Tests.ExternalPackage" and dependency != "Synthesis":
                errors.append(f"{module}: external conformance fixture must use only the public umbrella")
            if module.startswith("Tests.") and dependency.startswith("Synthesis.Internal."):
                errors.append(f"{module}: public conformance tests must not import internals")
            if module.startswith("Synthesis") and dependency.startswith("Tests."):
                errors.append(f"{module}: production module imports tests")
            layers = {
                "Core": {"Core"}, "Logic": {"Logic"}, "Systems": {"Systems"},
                "Physics": {"Core", "Physics"}, "IR": {"Core", "IR"},
                "Semantics": {"Core", "IR", "Logic", "Semantics"},
                "Design": {"Core", "IR", "Logic", "Semantics", "Design"},
                "Frontend": {"Core", "IR", "Logic", "Semantics", "Design", "Frontend"},
                "Interop": {"Core", "IR", "Logic", "Semantics", "Interop"},
            }
            layer = module.split(".")[1] if module.startswith("Synthesis.") else None
            kernel = module == "Synthesis" or layer in layers
            if layer in layers and dependency.startswith("Synthesis."):
                dependency_layer = dependency.split(".")[1]
                if dependency_layer not in layers[layer]:
                    errors.append(f"{module}: forbidden layer dependency on {dependency}")
            if layer in layers and dependency == "Synthesis":
                errors.append(f"{module}: internal layer imports kernel umbrella")
            if kernel and dependency.startswith(("Synthesis.Domains", "Synthesis.Bridges", "Synthesis.Examples")):
                errors.append(f"{module}: kernel imports a domain, bridge, or example")
            if module.startswith("Synthesis.Domains") and dependency.startswith(("Synthesis.Bridges", "Synthesis.Examples")):
                errors.append(f"{module}: domain imports a bridge or example")
            if module.startswith("Synthesis.Bridges") and dependency.startswith("Synthesis.Examples"):
                errors.append(f"{module}: bridge imports an example")
        if not text.endswith("\n") or "\r" in text or any(line.rstrip() != line for line in text.splitlines()):
            errors.append(f"{path.relative_to(ROOT)}: expected LF, final newline, and no trailing whitespace")

    visited: set[str] = set()
    active: set[str] = set()

    def visit(module: str) -> None:
        if module in active:
            errors.append(f"dependency cycle at {module}")
            return
        if module in visited:
            return
        active.add(module)
        for dependency in graph[module]:
            visit(dependency)
        active.remove(module)
        visited.add(module)

    visit("Tests.Audit")
    for module in modules.keys() - visited:
        errors.append(f"{module}: outside the audit import closure; add it to an umbrella or test import")
    if errors:
        print("\n".join(sorted(errors)), file=sys.stderr)
        return 1
    print(f"repository: {len(modules)} Lean modules covered by the audit; dependency boundaries passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
