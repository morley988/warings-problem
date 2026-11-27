import Waring.AuxiliaryScales
import Waring.CertificateGuards
import Mathlib.Tactic.NormNum

/-!
# Actual auxiliary coefficient count for the frozen degree-eight policy

The six rational scales are explicitly identified with the canonical policy
array. Their strict margins imply the genuine integer floor-box conditions,
and the actual six-block coefficient zero count has exponent 2.23249759.
The additional factor P in the F6 L2 estimate is a separate analytic input.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryFrozen
open AuxiliaryCounting AuxiliaryScales

def phi8Q : Array ℚ := #[(5793479/50000000 : ℚ),(11191889/100000000 : ℚ),
  (10604341/100000000 : ℚ),(9516681/100000000 : ℚ),(3846939/50000000 : ℚ),
  (806929/25000000 : ℚ)]

theorem phi8Q_eq_frozen : phi8Q = (Certificate.policies8[0]!).phi := by decide +kernel

def phi8 (i : ℕ) : ℝ := (phi8Q[i]! : ℚ)
def shiftExponent8 (i : ℕ) : ℝ := 1-8*phi8 i

theorem phi8_pos : ∀ i < 6, 0 < phi8 i := by
  intro i hi
  interval_cases i <;> norm_num [phi8,phi8Q]

theorem shiftExponent8_pos : ∀ i < 6, 0 < shiftExponent8 i := by
  intro i hi
  interval_cases i <;> norm_num [shiftExponent8,phi8,phi8Q]

theorem strict_prefix8 : ∀ i < 6,
    (∑ j ∈ Finset.range i, phi8 j) < shiftExponent8 i+phi8 i := by
  intro i hi
  interval_cases i <;> norm_num [shiftExponent8,phi8,phi8Q,Finset.sum_range_succ]

theorem block_exponent8 (i : ℕ) : 2*shiftExponent8 i+16*phi8 i=2 := by
  unfold shiftExponent8
  ring

theorem diagonal_exponent8 :
    (∑ i ∈ Finset.range 6, (shiftExponent8 i+phi8 i)) =
      (223249759/100000000 : ℝ) := by
  norm_num [shiftExponent8,phi8,phi8Q,Finset.sum_range_succ]

/-- All floor-cutoff prefix inequalities for the canonical six-block policy. -/
theorem eventually_frozen_prefix8 :
    ∀ᶠ P : ℝ in Filter.atTop, ∀ i < 6,
      (∏ j ∈ Finset.range i, floorScale P (phi8 j)) ≤
        floorScale P (shiftExponent8 i)*floorScale P (phi8 i) :=
  eventually_floor_prefix_le shiftExponent8 phi8 6 shiftExponent8_pos phi8_pos strict_prefix8

/-- The actual frozen-scale arithmetic auxiliary count, with no source estimate
or assumed finite recurrence. The power sixteen and six blocks are literal. -/
theorem frozen_depth6_zeroCount {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      (zeroCount 16 (prefixFamily (fun i => floorScale P (shiftExponent8 i))
        (fun i => floorScale P (phi8 i)) 6) : ℝ) ≤
        C*P^((223249759/100000000 : ℝ)+ε) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := auxiliary_zeroCount_real_scales 16 6 (by norm_num)
    shiftExponent8 phi8 (show (0 : ℝ) ≤ 2 by norm_num) hε
    shiftExponent8_pos phi8_pos strict_prefix8
    (by intro i hi; norm_num only [Nat.cast_ofNat]; exact le_of_eq (block_exponent8 i))
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hP
  simpa only [diagonal_exponent8] using hbound P hP

#print axioms phi8Q_eq_frozen
#print axioms frozen_depth6_zeroCount
end Waring.AuxiliaryFrozen
