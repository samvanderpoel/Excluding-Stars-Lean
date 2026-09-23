#!/usr/bin/env python3
"""Build the public libraries and check their declarations and axiom boundary.

Requirements: Python 3 (standard library only), Lake, and the pinned Lean toolchain.
Run from any working directory; all checks execute in this repository.
"""

from pathlib import Path
import os
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


def run(*command):
    print("+ " + " ".join(command), flush=True)
    environment = os.environ.copy()
    # Resolve imports using this package, rather than a caller's Lean path override.
    environment.pop("LEAN_PATH", None)
    environment.pop("LEAN_SRC_PATH", None)
    subprocess.run(command, cwd=ROOT, env=environment, check=True)


def main():
    try:
        check_imports()
        run("lake", "build", *LIBRARIES)
        run("lake", "env", "lean", "verification/Main.lean")
        run("lake", "env", "lean", "verification/Audit.lean")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print("Verification failed: " + str(error), file=sys.stderr)
        return 1
    print("Verification passed: libraries, main declarations, axiom boundary, and import reachability.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
