import Waring.ResourceDifferencingCap

/-!
# Exact integer phase multipliers of the five selected source reductions

The quadratic multiplier is `3*A`, and the coefficient multiplier is
`4*A`. Both are fixed positive integers. On fixing the other parameters,
the i-th coefficient phase is a cubic sampling phase in h_i, exactly as
required by the coefficient sampling theorem.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SourcePhaseConstants
open PolynomialSumReduction

theorem quadratic_argument (A Γ : ℕ) (α : ℝ) :
    3*α*(A:ℝ)*(Γ:ℝ) = ((3*A:ℕ):ℝ)*((Γ:ℝ)*α) := by
  push_cast
  ring

theorem quadratic_multiplier_pos {A : ℕ} (hA : 0 < A) : 0 < 3*A := by omega

theorem coefficient_multiplier_pos {A : ℕ} (hA : 0 < A) : 0 < 4*A := by omega

theorem shift_product_pos {j : ℕ} (h : Fin j → ℕ) (U : ℕ)
    (hh : ∀ i, 0 < h i) (hU : 0 < U) : 0 < (∏ i, h i)*U :=
  Nat.mul_pos (Finset.prod_pos (fun i _ => hh i)) hU

/-- The coefficient factor really has cubic sampling in its own h_i;
all the other shifts occur in one fixed residual product. -/
theorem coefficient_argument_cubic {j : ℕ} (A U : ℕ) (α : ℝ)
    (h : Fin j → ℕ) (i : Fin j) :
    (4*α*(A:ℝ)*((∏ l, (h l:ℝ))*(U:ℝ)))*(h i:ℝ)^2 =
      (((4*A:ℕ):ℝ)*(((∏ l ∈ Finset.univ.erase i, h l)*U:ℕ):ℝ)*α)*(h i:ℝ)^3 := by
  have hp : (∏ l, (h l:ℝ)) = (h i:ℝ)*(∏ l ∈ Finset.univ.erase i, (h l:ℝ)) :=
    (Finset.mul_prod_erase Finset.univ (fun l => (h l:ℝ)) (Finset.mem_univ i)).symm
  rw [hp]
  push_cast
  ring

/-- Integer-frequency adapter for exact Fourier orthogonality. -/
theorem normalForm_integer_frequency {j : ℕ} (p : ℕ) (A Γ U : ℤ)
    (h m : Fin j → ℤ) (ξ : ℤ) :
    normalForm p (A:ℝ) (Γ:ℝ) (U:ℝ) (fun i => (h i:ℝ)) (fun i => (m i:ℝ)) (ξ:ℝ) =
      ((A*Γ*(3*ξ^2+U+4*∑ i, (h i)^2*(m i)^p):ℤ):ℝ) := by
  simp only [normalForm, coefficientPolynomial]
  push_cast
  rfl

/-- The degree-eight F6 polynomial in the original z coordinate. -/
theorem k8_j6_integer_frequency (h m : Fin 6 → ℤ) (z : ℤ)
    (hm : ∀ i, m i ≠ 0) :
    Differences.modifiedCenteredPower 8
      (parameters (fun i => (h i:ℝ)) (fun i => (m i:ℝ))) (z:ℝ) =
      ((430080*(∏ i, h i)*(3*z^2+∑ i, (h i)^2*(m i)^16):ℤ):ℝ) := by
  rw [reduction_k8_j6 _ _ _ (fun i => by exact_mod_cast hm i)]
  simp only [normalForm, coefficientPolynomial]
  push_cast
  ring

theorem degree8_j4_multipliers : 3*(26880:ℕ)=80640 ∧ 4*(26880:ℕ)=107520 := by norm_num
theorem degree8_j5_multipliers : 3*(53760:ℕ)=161280 ∧ 4*(53760:ℕ)=215040 := by norm_num
theorem degree8_j6_multipliers : 3*(107520:ℕ)=322560 ∧ 4*(107520:ℕ)=430080 := by norm_num
theorem degree9_j5_multipliers : 3*(483840:ℕ)=1451520 ∧ 4*(483840:ℕ)=1935360 := by norm_num
theorem degree9_j6_multipliers : 3*(967680:ℕ)=2903040 ∧ 4*(967680:ℕ)=3870720 := by norm_num

/-- The original F6 family is exactly the integer-frequency Fourier sum
used by the solution-counting argument. This is an equality before any
completion or absolute value. -/
theorem k8_j6_family_fourier (H M : Finset (Fin 6 → ℕ)) (a b : ℤ) (α : ℝ)
    (hm : ∀ m ∈ M, ∀ i, m i ≠ 0) :
    polynomialFamily 8 (H ×ˢ M)
      (fun hm' i => (hm'.1 i:ℝ)) (fun hm' i => (hm'.2 i:ℝ)) α a b =
      ∑ x ∈ H ×ˢ (M ×ˢ Finset.Icc a b),
        fourier (430080*(∏ i, (x.1 i:ℤ))*(3*x.2.2^2+
          ∑ i, (x.1 i:ℤ)^2*(x.2.1 i:ℤ)^16)) (α : AddCircle (1:ℝ)) := by
  classical
  unfold polynomialFamily UnseparatedDifferencing.familySum
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro m hmM
  apply Finset.sum_congr rfl
  intro z hz
  have hid := k8_j6_integer_frequency (fun i => (h i:ℤ)) (fun i => (m i:ℤ)) z
    (fun i => by dsimp; exact_mod_cast hm m hmM i)
  simp only [Int.cast_natCast] at hid
  rw [hid]
  exact exp_linear_eq_fourier α _

#print axioms coefficient_argument_cubic
#print axioms k8_j6_integer_frequency
#print axioms k8_j6_family_fourier

end Waring.SourcePhaseConstants
