#!/usr/bin/env python3
"""Inventory the public, example, and regression dependencies."""
import csv
import importlib.util
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("checks", HERE / "check-artifact.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
root = checks.ROOT
modules = checks.graph()
roots = {"public": ["GLang.Artifact"], "default": ["GLang"],
         "examples": [n for n in modules if n.startswith("GLang.Examples.")],
         "tests": [n for p in (root / "tests").glob("*.lean") for n in checks.imports(p)]}
reach = {label: checks.closure(names, modules) for label, names in roots.items()}
writer = csv.writer(sys.stdout, delimiter="\t", lineterminator="\n")
writer.writerow(["module", *roots, "direct_importers", "script_mentions", "status"])
scripts = {str(p.relative_to(root)): p.read_text(errors="replace")
           for p in (root / "scripts").iterdir() if p.is_file()}
for name in sorted(modules):
    parents = sorted(n for n, deps in modules.items() if name in deps)
    mentions = sorted(p for p, text in scripts.items() if name in text or name.replace(".", "/") in text)
    live = any(name in names for names in reach.values())
    writer.writerow([name, *[int(name in reach[label]) for label in roots],
                     ",".join(parents), ",".join(mentions),
                     "reachable" if live else "review required; not deletion evidence"])
