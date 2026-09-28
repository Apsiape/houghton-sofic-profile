"""Standalone verification entry point; no private repository dependencies."""
from pathlib import Path
import os
import subprocess
import sys
from collections import Counter
from fractions import Fraction
import gzip
import json

HERE = Path(__file__).resolve().parent
LEAN = HERE / "lean"
env = dict(os.environ, LEAN_PATH=str(LEAN))

def run(args, cwd=HERE, timeout=180):
    subprocess.run(args, cwd=cwd, env=env, check=True, timeout=timeout)

run([sys.executable, "collectioncheck.py"])
run([sys.executable, "verify.py"], cwd=HERE / "certificates")
with gzip.open(HERE / "certificates/out/certificates.json.gz", "rt") as stream:
    entries = {e["name"]: e for e in json.load(stream)["certificates"]}
C = [[4,0,1,8,4], [108,32,31,128,60], [204,68,64,384,144],
     [0,0,0,0,0], [36,12,14,84,36]]
for i, expected in enumerate(C, 1):
    counts = Counter(r for _,r,_ in entries[f"psi(r{i})"]["cells"])
    assert [counts[f"r{j}"] for j in range(1,6)] == expected
weights = list(map(Fraction, [1, Fraction(63,2), Fraction(338,5), 0, Fraction(29,2)]))
assert all(sum(a*b for a,b in zip(row, weights)) <= 130*w for row,w in zip(C,weights))
print("Certificate-to-matrix counts and exact rational multiplier verified.", flush=True)
run(["lean", "-M", "512", "-j", "1", "-T", "100000", "Arithmetic.lean"], cwd=LEAN)
run(["lean", "-M", "512", "-j", "1", "-T", "100000",
     "-o", "FreeReduction.olean", "FreeReduction.lean"], cwd=LEAN)
run([sys.executable, "generate_lean.py"])
run(["lean", "-M", "768", "-j", "1", "-T", "100000", "Certificates.lean"], cwd=LEAN, timeout=600)
print("All specified checks passed. This is not full formal verification of the paper.")
