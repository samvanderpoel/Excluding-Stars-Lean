#!/usr/bin/env python3
"""Build the public libraries and check their declarations and axiom boundary.

Requirements: Python 3 (standard library only), Lake, and the pinned Lean toolchain.
Run from any working directory; all checks execute in this repository.
"""

from pathlib import Path
import os
import json
import hashlib
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ("DenseGraph", "InducedStars")
IMPORT = re.compile(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)")


def without_comments_and_strings(source):
    """Mask Lean's nested comments and strings, preserving line boundaries."""
    output = []
    index, depth = 0, 0
    in_string, escaped = False, False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
                output.append("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
        elif in_string:
            output.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
        elif pair == "--":
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            output.append(" " * (end - index))
            index = end
        elif pair == "/-":
            depth = 1
            output.append("  ")
            index += 2
        else:
            in_string = char == '"'
            output.append(" " if in_string else char)
            index += 1
    if depth or in_string:
        raise ValueError("unterminated Lean comment or string")
    return "".join(output)


def check_imports():
    """Require every shipped implementation module to be reachable from its root."""
    paths = {}
    for library in LIBRARIES:
        root = ROOT / (library + ".lean")
        if not root.is_file():
            raise ValueError("missing curated root: " + str(root))
        for path in [root, *sorted((ROOT / library).rglob("*.lean"))]:
            if not path.resolve().is_relative_to(ROOT):
                raise ValueError("project source escapes the repository: " + str(path))
            module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
            paths[module] = path
    graph = {}
    for module, path in paths.items():
        source = without_comments_and_strings(path.read_text(encoding="utf-8"))
        imports = [name for line in IMPORT.findall(source) for name in line.split()]
        local = [name for name in imports
                 if name.split(".", 1)[0] in LIBRARIES]
        missing = set(local) - paths.keys()
        if missing:
            raise ValueError(module + " imports missing modules: " + ", ".join(sorted(missing)))
        graph[module] = local
    for library in LIBRARIES:
        reached, pending = set(), [library]
        while pending:
            module = pending.pop()
            if module not in reached:
                reached.add(module)
                pending.extend(graph[module])
        expected = {name for name in paths if name.split(".", 1)[0] == library}
        missing = expected - reached
        if missing:
            raise ValueError(library + " does not reach: " + ", ".join(sorted(missing)))
        print(f"{library}: all {len(expected)} library modules reachable", flush=True)


def check_current_corpus():
    """Check the reviewed source-map inventory and manuscript exclusion."""
    manifest = json.loads((ROOT / "docs/current-source-map.json").read_text())
    rows = manifest["modules"]
    expected = {row["path"]: row for row in rows}
    if len(expected) != len(rows):
        raise ValueError("duplicate source-map path")
    actual = set()
    for library in LIBRARIES:
        actual.add(library + ".lean")
        actual.update(str(p.relative_to(ROOT)) for p in (ROOT / library).rglob("*.lean"))
    if actual != expected.keys():
        raise ValueError("source-map inventory differs from the shipped Lean corpus")
    for relative, row in expected.items():
        path = ROOT / relative
        if path.is_symlink() or not path.resolve().is_relative_to(ROOT):
            raise ValueError("nonlocal or linked mathematical source: " + relative)
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != row["sha256"]:
            raise ValueError("source-map hash mismatch: " + relative)
        if not row["current_paper_labels"] or not row["role"]:
            raise ValueError("missing current-paper traceability: " + relative)
    digest = hashlib.sha256("".join(
        relative + "\0" + expected[relative]["sha256"] + "\n"
        for relative in sorted(expected)).encode()).hexdigest()
    if digest != manifest["source_tree_sha256"]:
        raise ValueError("source-map tree digest mismatch")
    private_names = {"paper", "AGENTS.md", ".agents", "blueprint",
                     "formalization-notes", "formalization-audit",
                     "references", "source-material", ".revision-work"}
    present = private_names & {p.name for p in ROOT.iterdir()}
    if present:
        raise ValueError("excluded private/manuscript paths: " + ", ".join(sorted(present)))
    for base, directories, files in os.walk(ROOT, followlinks=False):
        directories[:] = [name for name in directories if name not in
                          {".git", ".lake", "__pycache__"}]
        for name in files:
            path = Path(base) / name
            if path.suffix.lower() in {".tex", ".pdf", ".bib", ".synctex"} or name.endswith(".synctex.gz"):
                raise ValueError("manuscript artifact in release: " + str(path.relative_to(ROOT)))
            if path.suffix == ".lean" and str(path.relative_to(ROOT)) not in actual | {
                    "verification/Main.lean", "verification/Audit.lean"}:
                raise ValueError("unmapped Lean source: " + str(path.relative_to(ROOT)))
    print(f"Current-paper source map: {len(expected)} files; no manuscript assets", flush=True)


def run(*command):
    print("+ " + " ".join(command), flush=True)
    environment = os.environ.copy()
    # Resolve imports using this package, rather than a caller's Lean path override.
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    subprocess.run(command, cwd=ROOT, env=environment, check=True)


def main():
    try:
        check_current_corpus()
        check_imports()
        run("lake", "build", *LIBRARIES)
        run("lake", "env", "lean", "verification/Main.lean")
        run("lake", "env", "lean", "verification/Audit.lean")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print("Verification failed: " + str(error), file=sys.stderr)
        return 1
    print("Verification passed: libraries, main declarations, axiom boundary, import reachability, and current-corpus manifest.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
