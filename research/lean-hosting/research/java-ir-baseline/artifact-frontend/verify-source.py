#!/usr/bin/env python3
"""Current relocation-layer audit. Historical verifier source remains in Git."""
from pathlib import Path
import runpy
root = next(p for p in Path(__file__).resolve().parents
            if (p / "history/relocations-v1.json").is_file())
runpy.run_path(str(root / "history/verify_relocations.py"), run_name="__main__")
