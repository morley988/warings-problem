import WaringSiegel.WSL2MomentVinogradov

/-! # Inserting an ordinary variable into an even restricted moment

Finite Fourier orthogonality and positivity of the coefficients permit one
copy of a restricted sum in the full-torus moment to be enlarged. The
pointwise comparison is required only after expanding the integral.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate
open WaringSiegel WaringSiegel.WSL2

namespace WaringLinear

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem frequency_product (v : α → ι → ℤ) (u : β → ι → ℤ)
    (a : α → ℂ) (b : β → ℂ) (θ : ι → AddCircle (1 : ℝ)) :
    frequencySum v a θ * frequencySum u b θ =
      frequencySum (fun p : α × β => v p.1 + u p.2)
        (fun p => a p.1 * b p.2) θ := by
  simp only [frequencySum, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
    WaringSiegel.latticeCharacter_add]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- The mixed integral with one ordinary coefficient family, in collision form. -/
theorem mixed_integral_expansion (v : α → ι → ℤ) (a b : α → ℝ) (s : ℕ) :
    (∫ θ, (frequencySum v (fun x => (b x : ℂ)) θ *
        frequencySum v (fun x => (a x : ℂ)) θ^s) *
        conj (frequencySum v (fun x => (a x : ℂ)) θ^(s+1)) ∂latticeHaar).re =
      ∑ p : (α × (Fin s → α)) × (Fin (s+1) → α),
        if v p.1.1 + (∑ i, v (p.1.2 i)) = ∑ i, v (p.2 i)
        then (b p.1.1 * ∏ i, a (p.1.2 i)) * ∏ i, a (p.2 i) else 0 := by
  simp_rw [frequencySum_pow, frequency_product]
  rw [integral_frequencySum_mul_conj, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp [← Complex.ofReal_prod, ← Complex.ofReal_mul]

/-- Enlarging a single positive coefficient family bounds the even restricted
moment by a mixed absolute moment over the full torus in every dimension. -/
theorem even_moment_le_one_mixed (v : α → ι → ℤ) (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (s : ℕ) :
    (∫ θ, ‖frequencySum v (fun x => (a x : ℂ)) θ‖^(2*(s+1)) ∂latticeHaar) ≤
      ∫ θ, ‖frequencySum v (fun x => (b x : ℂ)) θ‖ *
        ‖frequencySum v (fun x => (a x : ℂ)) θ‖^(2*s+1) ∂latticeHaar := by
  let F := frequencySum v (fun x => (a x : ℂ))
  let f := frequencySum v (fun x => (b x : ℂ))
  have hbase : (∫ θ, ‖F θ‖^(2*(s+1)) ∂latticeHaar) =
      (∫ θ, (F θ * F θ^s) * conj (F θ^(s+1)) ∂latticeHaar).re := by
    have h (θ) : (F θ * F θ^s) * conj (F θ^(s+1)) =
        ((‖F θ‖^(2*(s+1)) : ℝ) : ℂ) := by
      rw [← pow_succ', Complex.mul_conj', norm_pow, ← Complex.ofReal_pow, ← pow_mul, Nat.mul_comm]
    simp_rw [h]
    rw [integral_complex_ofReal]
    rfl
  have hcompare : (∫ θ, (F θ * F θ^s) * conj (F θ^(s+1)) ∂latticeHaar).re ≤
      (∫ θ, (f θ * F θ^s) * conj (F θ^(s+1)) ∂latticeHaar).re := by
    unfold F f
    rw [mixed_integral_expansion, mixed_integral_expansion]
    apply Finset.sum_le_sum
    intro p _
    split_ifs
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hab _) (Finset.prod_nonneg (fun _ _ => ha _)))
        (Finset.prod_nonneg (fun _ _ => ha _))
    · exact le_rfl
  change (∫ θ, ‖F θ‖^_ ∂latticeHaar) ≤ ∫ θ, ‖f θ‖ * ‖F θ‖^_ ∂latticeHaar
  calc
    _ = _ := hbase
    _ ≤ _ := hcompare
    _ ≤ _ := Complex.re_le_norm _
    _ ≤ _ := norm_integral_le_integral_norm _
    _ = _ := by
      congr 1
      funext θ
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_conj, norm_pow, mul_assoc, ← pow_add]
      congr 2
      omega

#print axioms even_moment_le_one_mixed

end WaringLinear
