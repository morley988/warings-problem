import WaringSiegel.WSL4WeilFiniteField

/-! # WSL4: literal mixed cubic sums over finite fields

The leading cubic coefficient must be nonzero, the additive character must be
nontrivial, and the characteristic must differ from three.  The linear twist is
arbitrary, and the field can have any residue degree.
-/

noncomputable section
namespace WaringSiegel.WSL4Weil
open Polynomial Finset

theorem natDegree_mixed_cubic {F : Type*} [Field F] {a : F} (ha : a ≠ 0) (b : F) :
    (C a * X ^ 3 + C b * X : F[X]).natDegree = 3 := by
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_C_mul_X_pow _ _ ha]
  rw [natDegree_C_mul_X_pow _ _ ha]
  have hb := natDegree_C_mul_X_pow_le b 1
  simpa only [pow_one] using lt_of_le_of_lt hb (by norm_num : 1 < 3)

/-- The mixed cubic Weil bound, with an arbitrary linear twist. -/
theorem norm_sum_mixed_cubic_le
    {F : Type*} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F]
    (hp : p ≠ 3) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) {a : F} (ha : a ≠ 0) (b : F) :
    ‖∑ x : F, ψ (a * x ^ 3 + b * x)‖ ≤ 2 * √(Fintype.card F) := by
  have hpm : ¬p ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp h
  have hb := norm_sum_addChar_eval_finiteField_le p hψ
    (f := C a * X ^ 3 + C b * X)
    (by rw [natDegree_mixed_cubic ha]; norm_num)
    (by rwa [natDegree_mixed_cubic ha])
  simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X, natDegree_mixed_cubic ha,
    Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] using hb

/-- The same bound with the characteristic taken canonically from the field. -/
theorem norm_sum_mixed_cubic_le_of_char_ne_three
    {F : Type*} [Field F] [Fintype F]
    (hchar : ringChar F ≠ 3) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    {a : F} (ha : a ≠ 0) (b : F) :
    ‖∑ x : F, ψ (a * x ^ 3 + b * x)‖ ≤ 2 * √(Fintype.card F) := by
  letI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.prime_ringChar F⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  exact norm_sum_mixed_cubic_le (ringChar F) hchar hψ ha b

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.norm_sum_mixed_cubic_le
#print axioms WaringSiegel.WSL4Weil.norm_sum_mixed_cubic_le_of_char_ne_three
