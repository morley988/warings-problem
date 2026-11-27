import WaringSiegel.WSL3PoissonCoprimeWeyl

/-! # Exact fourth-power transfer to a prime-coprimality mask -/
noncomputable section
open NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem finiteLinearTraceSum_coprime_prime_fourth_bound
    (S : Finset (𝓞 K)) (f : 𝓞 K → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ q, ‖finiteLinearTraceSum S f q‖^4 ≤ B)
    (p : ℕ) (hp : p.Prime) (q : ArchimedeanTraceTorus K) :
    ‖finiteLinearTraceSum (S.filter (fun x =>
      IsUnit (Ideal.Quotient.mk (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) x))) f q‖^4 ≤
      ((2 : ℝ)^finrank ℚ K)^4 * B := by
  let b := Real.sqrt (Real.sqrt B)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb4 : b^4 = B := by
    calc
      b^4 = (b^2)^2 := by ring
      _ = (Real.sqrt B)^2 := by rw [show b^2 = Real.sqrt B from Real.sq_sqrt (Real.sqrt_nonneg B)]
      _ = B := Real.sq_sqrt hB0
  have hroot : ∀ q, ‖finiteLinearTraceSum S f q‖ ≤ b := by
    intro q
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hb
    rw [hb4]
    exact hB q
  have h := finiteLinearTraceSum_coprime_prime_bound S f b hroot p hp q
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h 4
  simpa only [mul_pow,hb4] using h4

#print axioms finiteLinearTraceSum_coprime_prime_fourth_bound
end WaringSiegel.WSL4Local
