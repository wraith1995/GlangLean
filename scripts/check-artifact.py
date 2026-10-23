#!/usr/bin/env python3
"""Build the formalization and check public theorem axioms and regression examples."""
import argparse
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]

def imports(path):
    return re.findall(r"^import\s+([\w.]+)", path.read_text(), re.M)

def graph():
    return {".".join(p.relative_to(ROOT).with_suffix("").parts): imports(p)
            for p in [ROOT / "GLang.lean", *sorted((ROOT / "GLang").rglob("*.lean"))]}

def closure(roots, modules):
    found, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name not in found:
            found.add(name)
            pending.extend(modules.get(name, []))
    return found

def run(args, env=None):
    print("+ " + " ".join(map(str, args)), flush=True)
    subprocess.run(args, cwd=ROOT, check=True, env=env)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=("core", "maintenance"), default="core")
    parser.add_argument("--full-build", action="store_true", help="also check the default library target")
    args = parser.parse_args()
    started = time.monotonic()
    modules = graph()
    tests = []
    core = {"PublicAxioms", "FrozenPaperSurface", "StrictValueAccess", "StrictValueShapes",
            "BinaryValueApplication", "TangentCoordinates", "TangentAreaOptimization"}
    for path in sorted((ROOT / "tests").glob("*.lean")):
        if (args.suite == "core" and path.stem in core or
            args.suite == "maintenance"):
            tests.append(path)
    targets = {"GLang.Artifact"}
    for path in tests:
        targets.update(n for n in imports(path) if n.startswith("GLang"))
    if args.full_build:
        targets.add("GLang")
    run(["lake", "build", *sorted(targets)])
    for path in tests:
        run(["lake", "env", "lean", str(path.relative_to(ROOT))])
    run(["bash", "scripts/check-sorries.sh"])
    # Primitive surface syntax/judgments may not import the annotated syntax.
    for root in ("GLang.Surface.Syntax", "GLang.Surface.Judgments", "GLang.Surface.Context"):
        if root in modules:
            bad = {"GLang.Annotated.Syntax", "GLang.Annotated.Judgments"} & closure([root], modules)
            if bad:
                raise SystemExit(f"{root} imports annotated definitions: {sorted(bad)}")
    print(f"PASS: {args.suite}; {len(tests)} regressions; {time.monotonic()-started:.1f}s", flush=True)

if __name__ == "__main__":
    main()
