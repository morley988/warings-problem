# Waring and Waring–Siegel in Lean

The arithmetic and integer-order certificates for the 6.873 coefficient are kernel-checked. The corresponding classical and number-field representation theorems expose their remaining analytic hypotheses in their Lean statements.

The source develops classical and number-field Waring bounds, their local obstructions, and the conductor and moment estimates used in the linear-bound argument. It uses Lean 4.24.0 and mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

[Mathematical scope](FORMALIZATION.md) · [Aggregate import](WaringLinear.lean) · [Source attribution](NOTICE.txt)

## Build and verification

With Elan, Git, Python 3 and the pinned toolchain installed, run these commands from the project directory.

```sh
lake exe cache get
python3 verification-scripts/replay.py --fresh
```

The script compiles each project module in dependency order using one Lean worker and runs the axiom audit. The optional historical sources contain the two closed classical bounds in degrees eight and nine. Include them and their endpoint audit with `python3 verification-scripts/replay.py --fresh --historical`. The standard Lake target is also available.

```sh
lake build WaringLinear
```

The numerical certificates are explicit Lean terms checked by kernel reduction. The verification directory contains the source inventory, SHA-256 file hashes and theorem dependency reports. The file `verification/audit-scope.json` identifies the import set covered by the most recent aggregate audit and records how to repeat the check on the entire release.
