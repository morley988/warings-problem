import Lean

/-! A finite obstruction for twelfth powers in ℤ₂[√2]. A pair is the
pair of coefficients on 1 and √2 reduced modulo 32. The residue of the
rational coordinate modulo 16 counts the unit roots. -/

namespace WaringLinear.SqrtTwoTwelve

abbrev Root := Fin 32 × Fin 32

/-- Multiplication in (ℤ/32ℤ)[T]/(T²−2) on the least residues. -/
def multiply (x y : Nat × Nat) : Nat × Nat :=
  ((x.1 * y.1 + 2*x.2*y.2) % 32, (x.1*y.2 + x.2*y.1) % 32)

def twelfthPower (x : Root) : Nat × Nat :=
  let y := (x.1.val, x.2.val)
  let sq := multiply y y
  let fourth := multiply sq sq
  multiply (multiply fourth fourth) fourth

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem powerImage : ∀ a b : Fin 32,
    (twelfthPower (a,b)).1 % 16 = a.val % 2 ∧
    (a.val % 2 = 0 → (twelfthPower (a,b)).1 = 0) := by decide

def scalarSum (xs : List Root) : Nat :=
  (xs.map (fun x => (twelfthPower x).1)).sum

def unitCount (xs : List Root) : Nat :=
  (xs.map (fun x => x.1.val % 2)).sum

private theorem scalar_mod (xs : List Root) :
    scalarSum xs % 16 = unitCount xs % 16 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨a,b⟩
    change ((twelfthPower (a,b)).1 + scalarSum ys) % 16 =
      (a.val % 2 + unitCount ys) % 16
    rw [Nat.add_mod, (powerImage a b).1, ih]
    rw [Nat.add_mod (a.val % 2) (unitCount ys) 16]
    have hh : a.val % 2 < 16 := by omega
    rw [Nat.mod_eq_of_lt hh]

private theorem unitCount_le (xs : List Root) : unitCount xs ≤ xs.length := by
  induction xs with
  | nil => decide
  | cons y ys ih =>
    change y.1.val % 2 + unitCount ys ≤ ys.length + 1
    omega

private theorem scalar_zero (xs : List Root) (hu : unitCount xs = 0) :
    scalarSum xs = 0 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨a,b⟩
    change a.val % 2 + unitCount ys = 0 at hu
    change (twelfthPower (a,b)).1 + scalarSum ys = 0
    rw [(powerImage a b).2 (by omega), ih (by omega)]

/-- The rational coefficient 16 (modulo 32) cannot be obtained with
fewer than sixteen summands, even with no restriction on the second
coordinate of the target. -/
theorem at_least_sixteen (xs : List Root) (ht : scalarSum xs % 32 = 16) :
    16 ≤ xs.length := by
  have h := scalar_mod xs
  have hlen := unitCount_le xs
  by_cases hc : 16 ≤ xs.length
  · exact hc
  · have hu : unitCount xs = 0 := by omega
    have hz := scalar_zero xs hu
    omega

#print axioms at_least_sixteen
end WaringLinear.SqrtTwoTwelve
