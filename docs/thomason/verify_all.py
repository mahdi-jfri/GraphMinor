#!/usr/bin/env python3
"""Run the two exact certificate checkers of the note uniform_minor_bound.pdf.

Requires Python 3.8 or later and no other package.
"""

from pathlib import Path
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parent
    pairs = (
        ("global_finite_checker.py", "global_finite_certificate.jsonl"),
        ("global_medium_checker.py", "global_medium_certificate.jsonl"),
    )
    for checker, certificate in pairs:
        subprocess.run(
            [sys.executable, str(root / checker), "check", str(root / certificate)],
            cwd=str(root),
            check=True,
        )
    print("PASS: both exact certificates verified.", flush=True)
    print("Together they cover all integers 51 <= p <= 10^44.", flush=True)
    print("Section 6 of the note covers ln(p) >= 100, which includes every p > 10^44.", flush=True)


if __name__ == "__main__":
    main()
