"""Mutation tests for the certificate verifiers: corrupted archives must be rejected.

Each test builds a corrupted copy of an archive in a temporary directory, runs the verifier on it in normal
mode and under python -O, and requires a nonzero exit status in both modes. The tests cover:
  - verify107.py with the original-relator cells of the D3 certificate deleted;
  - verify.py with an empty certificate list;
  - verify.py with one certificate missing;
  - verify.py with one certificate duplicated.
The distributed archives themselves are never modified.
"""
import gzip
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def run(args, cwd):
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=300).returncode


def load(name):
    with gzip.open(HERE / "out" / name, "rt") as stream:
        return json.load(stream)


def dump(data, path):
    with gzip.open(path, "wt", encoding="ascii") as stream:
        json.dump(data, stream)


def rejected_in_both_modes(script, args, cwd):
    return all(run([sys.executable] + mode + [str(script)] + args, cwd) != 0 for mode in ([], ["-O"]))


def main():
    failures = []
    with tempfile.TemporaryDirectory(prefix="certificate-mutations-") as tmp:
        work = Path(tmp)
        (work / "out").mkdir()
        shutil.copy2(HERE / "verify107.py", work / "verify107.py")
        data = load("certificates107.json.gz")
        hits = [e for e in data["certificates"] if e["name"] == "D3"]
        if len(hits) != 1:
            raise SystemExit("expected exactly one D3 certificate")
        hits[0]["cells"] = []
        dump(data, work / "out" / "certificates107.json.gz")
        if not rejected_in_both_modes(work / "verify107.py", [], work):
            failures.append("verify107.py accepted the D3 certificate with its cells deleted")

        original = load("certificates.json.gz")
        cases = {
            "an empty certificate list": {"certificates": []},
            "one certificate missing": {"certificates": original["certificates"][1:]},
            "one certificate duplicated": {"certificates": original["certificates"] + original["certificates"][:1]},
        }
        for label, archive in cases.items():
            path = work / "mutated.json.gz"
            dump(archive, path)
            if not rejected_in_both_modes(HERE / "verify.py", [str(path)], work):
                failures.append("verify.py accepted " + label)

    for f in failures:
        print("MUTATION ACCEPTED:", f)
    if failures:
        sys.exit(1)
    print("All mutations rejected in normal and optimized mode.")


if __name__ == "__main__":
    main()
