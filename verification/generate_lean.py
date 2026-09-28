"""Deterministically transcribe the distributed certificate data into Lean.

The Lean kernel, not this generator, checks every emitted free-word equality.
The independent Python verifier supplies targets from manuscript definitions;
this translation is explicitly part of the input/provenance boundary.
Run from any directory: python verification/generate_lean.py
"""
import gzip
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
AUX107 = '--aux107' in sys.argv
DATA = ROOT / "certificates" / "out" / ("certificates107.json.gz" if AUX107 else "certificates.json.gz")
spec = importlib.util.spec_from_file_location("independent_verifier", ROOT / "certificates" / ("verify107.py" if AUX107 else "verify.py"))
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)

def quoted_word(w):
    assert set(w) <= set("aAbBxX")
    return 'word "' + w + '"'

def main():
    assert DATA.stat().st_size < 2_000_000
    with gzip.open(DATA, "rt", encoding="ascii") as f:
        entries = json.load(f)["certificates"]
    # Core finite relations; recursion instances remain executable Python checks.
    if not AUX107:
        entries = entries[:next(i for i, e in enumerate(entries) if e["name"].startswith("X_"))]
    else:
        entries = [e for e in entries if not e['name'].startswith('h')]
    # Keep the default kernel replay bounded. All 40 certificates, including
    # the longer relator images, are checked by the independent Python verifier.
    entries = [e for e in entries if len(e["cells"]) <= 21]
    lines = [
        "import FreeReduction",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "namespace WordCertificate",
        '-- Generated from SHA-256 ' + hashlib.sha256(DATA.read_bytes()).hexdigest(),
        "def word (s : String) : Word := s.toList.map fun c =>",
        "  match c with",
        "  | 'a' => .a | 'A' => .A | 'b' => .b | 'B' => .B | 'x' => .x | _ => .X",
    ]
    for n, e in enumerate(entries):
        lines.append("-- " + e["name"])
        lines.append(f"def cells_{n} : List Cell := [")
        cells = []
        for z, r, sign in e["cells"]:
            assert r in verifier.REL and sign in (-1, 1)
            z = verifier.red(z)
            cells.append(f"  ⟨{quoted_word(z)}, {int(r[1:])-1}, {'true' if sign == -1 else 'false'}⟩")
        lines.append(",\n".join(cells) + "]")
        target = verifier.target(e["name"])
        lines += [
            f"def target_{n} : Word := {quoted_word(target)}",
            f"theorem area_count_{n} : cells_{n}.length = {len(e['cells'])} := by decide",
            f'theorem step_{n}_0 (M : Model G) (_h : ∀ i, eval M (relator i) = M.one) :',
            '    eval M (word "") = M.one := rfl',
        ]
        tail = ""
        for index, (z, rel, sign) in enumerate(reversed(e["cells"]), 1):
            z = verifier.red(z)
            rr = verifier.REL[rel]
            rr = rr if sign == 1 else verifier.inv(rr)
            current = verifier.red(z + rr + verifier.inv(z) + tail)
            c = f"⟨{quoted_word(z)}, {int(rel[1:])-1}, {'true' if sign == -1 else 'false'}⟩"
            lines += [
                f"theorem step_{n}_{index} (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :",
                f"    eval M ({quoted_word(current)}) = M.one :=",
                f"  checked_step M h {c} ({quoted_word(tail)}) ({quoted_word(current)})",
                f"    (by decide) (step_{n}_{index-1} M h)",
            ]
            tail = current
        assert tail == verifier.red(target)
        lines += [
            f"theorem semantic_{n} (M : Model G) (h : ∀ i, eval M (relator i) = M.one) :",
            f"    eval M target_{n} = M.one := by",
            f"  have endcheck : reduce target_{n} = reduce ({quoted_word(tail)}) := by decide",
            f"  exact (reduction_equality_sound M _ _ endcheck).trans (step_{n}_{len(e['cells'])} M h)",
            f"#check semantic_{n}",
        ]
    lines += [f"#print axioms semantic_{n}", "end WordCertificate", ""]
    output = ROOT / "lean" / ("Certificates107.lean" if AUX107 else "Certificates.lean")
    output.write_text("\n".join(lines), encoding="utf-8")
    print(f"Transcribed {len(entries)} core certificates to {output.name}")

if __name__ == "__main__":
    main()
