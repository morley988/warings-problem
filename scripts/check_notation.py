"""Check the notation for positive summands in the Waring manuscripts."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PLUS = r"(?:\^\s*(?:\{\s*\+\s*\}|\+)|⁺)"
FIELD = r"(?:[KLF𝕂𝕃𝔽]|\\(?:mathbb\s*\{?[KLF]\}?|[KLF](?![A-Za-z])))"
SUB = rf"_\s*(?:\{{\s*{FIELD}(?:_[A-Za-z0-9]+)?\s*\}}|{FIELD})"
OBSOLETE = re.compile(rf"(?<![A-Za-z])G\s*(?:{PLUS}\s*{SUB}|{SUB}\s*{PLUS})")


def main():
    hits = []
    for directory in ("manuscript", "supplements"):
        for path in sorted((ROOT / directory).rglob("*.tex")):
            for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                if OBSOLETE.search(line):
                    hits.append(f"{path.relative_to(ROOT)}:{number}")
    if hits:
        raise SystemExit("Review the field-indexed superscript in " + ", ".join(hits))
    print("Waring manuscript notation passed.")


if __name__ == "__main__":
    main()
