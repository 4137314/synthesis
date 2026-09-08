#!/usr/bin/env python3
"""Extract the complete public project API serially with the pinned doc-gen4 CLI."""
from pathlib import Path
import posixpath
import re
import subprocess
from urllib.parse import urlsplit, urlunsplit

ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "docbuild/.lake/build/api"
OUTPUT = BUILD / "doc"
GENERATOR = ROOT / ".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
UPSTREAM = "https://leanprover-community.github.io/mathlib4_docs/"


def run(*arguments: str) -> None:
    subprocess.run([str(GENERATOR), *arguments], check=True)


def main() -> None:
    BUILD.mkdir(parents=True, exist_ok=True)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    origin = subprocess.check_output(["git", "remote", "get-url", "origin"], cwd=ROOT, text=True).strip()
    if origin.startswith("git@github.com:"):
        origin = origin.replace("git@github.com:", "https://github.com/", 1)
    origin = origin.removesuffix(".git")
    if not origin.startswith("https://github.com/"):
        raise SystemExit("API source links require a GitHub origin")
    sources = [ROOT / "Synthesis.lean", *sorted((ROOT / "Synthesis").rglob("*.lean"))]
    sources = [p for p in sources if "Examples" not in p.parts]
    run("bibPrepass", "--build", str(BUILD), "--none")
    for source in sources:
        relative = source.relative_to(ROOT)
        module = ".".join(relative.with_suffix("").parts)
        print(f"Documenting {module}", flush=True)
        run("single", "--build", str(BUILD), module, "api-docs.db",
            f"{origin}/blob/{commit}/{relative.as_posix()}")
    run("fromDb", "--build", str(BUILD), "--manifest", str(BUILD / "doc-manifest.json"),
        str(BUILD / "api-docs.db"), "Synthesis", "Synthesis.Domains", "Synthesis.Bridges")
    # Imported modules have placeholder pages; link to their actual upstream APIs.
    external_roots = {"Mathlib", "Lean", "Init", "Std", "Lake", "Batteries", "Aesop", "Qq",
                      "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient"}
    for page in OUTPUT.rglob("*.html"):
        directory = page.parent.relative_to(OUTPUT).as_posix()
        def link(match: re.Match[str]) -> str:
            value = match.group(1)
            uri = urlsplit(value)
            if uri.scheme or uri.netloc or not uri.path.endswith(".html"):
                return match.group(0)
            target = posixpath.normpath(posixpath.join(directory, uri.path))
            if target.split("/")[0].removesuffix(".html") in external_roots:
                return 'href="' + urlunsplit((*urlsplit(UPSTREAM)[:2], "/mathlib4_docs/" + target, uri.query, uri.fragment)) + '"'
            return match.group(0)
        page.write_text(re.sub(r'href="([^"]+)"', link, page.read_text(encoding="utf-8")), encoding="utf-8")
    (OUTPUT / ".nojekyll").touch()
    print(f"Generated {len(sources)} project modules; dependency APIs link to {UPSTREAM}")


if __name__ == "__main__":
    main()
