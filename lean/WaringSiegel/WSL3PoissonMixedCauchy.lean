import WaringSiegel.WSL3PoissonMixedHolder

/-! # Exact weighted Cauchy inequality for the mixed aggregate

The integrand may be complex. Its pointwise positivity is neither assumed
nor asserted. Only the real weights and the common fourth-power factor are
nonnegative.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL3Poisson

section Compact
variable {Ω α : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  [CompactSpace Ω] [Fintype α] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem compact_weighted_sum_integral_cauchy
    (u : α → ℝ) (hu : ∀ a, 0 ≤ u a)
    (F G : α → Ω → ℂ) (hF : ∀ a, Continuous (F a)) (hG : ∀ a, Continuous (G a))
    (V : Ω → ℝ) (hV : Continuous V) (hV0 : ∀ x, 0 ≤ V x) :
    ‖∫ x, (∑ a : α, (u a:ℂ)*F a x*G a x)*(V x:ℂ) ∂μ‖^2 ≤
      (∫ x, (∑ a : α, u a*‖F a x‖^2)*V x ∂μ)*
        (∫ x, (∑ a : α, u a*‖G a x‖^2)*V x ∂μ) := by
  let A : Ω → ℝ := fun x => (∑ a : α, u a*‖F a x‖^2)*V x
  let B : Ω → ℝ := fun x => (∑ a : α, u a*‖G a x‖^2)*V x
  let T : Ω → ℝ := fun x => (∑ a : α, u a*‖F a x‖*‖G a x‖)*V x
  let S : Ω → ℂ := fun x => (∑ a : α, (u a:ℂ)*F a x*G a x)*(V x:ℂ)
  have hA : Continuous A :=
    (continuous_finset_sum _ (fun a _ => continuous_const.mul ((hF a).norm.pow 2))).mul hV
  have hB : Continuous B :=
    (continuous_finset_sum _ (fun a _ => continuous_const.mul ((hG a).norm.pow 2))).mul hV
  have hT : Continuous T :=
    (continuous_finset_sum _ (fun a _ => (continuous_const.mul (hF a).norm).mul (hG a).norm)).mul hV
  have hS : Continuous S :=
    (continuous_finset_sum _ (fun a _ => (continuous_const.mul (hF a)).mul (hG a))).mul
      (Complex.continuous_ofReal.comp hV)
  have hA0 (x : Ω) : 0 ≤ A x :=
    mul_nonneg (Finset.sum_nonneg (fun a _ => mul_nonneg (hu a) (sq_nonneg _))) (hV0 x)
  have hB0 (x : Ω) : 0 ≤ B x :=
    mul_nonneg (Finset.sum_nonneg (fun a _ => mul_nonneg (hu a) (sq_nonneg _))) (hV0 x)
  have hT0 (x : Ω) : 0 ≤ T x :=
    mul_nonneg (Finset.sum_nonneg (fun a _ => mul_nonneg (mul_nonneg (hu a) (norm_nonneg _))
      (norm_nonneg _))) (hV0 x)
  have hnorm (x : Ω) : ‖S x‖ ≤ T x := by
    dsimp [S,T]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hV0 x)]
    apply mul_le_mul_of_nonneg_right _ (hV0 x)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a _
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu a),le_refl]
  have hsq (x : Ω) : T x^2 ≤ A x*B x := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s:=Finset.univ)
      (f:=fun a => u a*‖F a x‖^2) (g:=fun a => u a*‖G a x‖^2)
      (r:=fun a => u a*‖F a x‖*‖G a x‖)
      (fun a _ => mul_nonneg (hu a) (sq_nonneg _))
      (fun a _ => mul_nonneg (hu a) (sq_nonneg _)) (fun a _ => by ring)
    simpa only [A,B,T,mul_pow,pow_two,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_right hcs (sq_nonneg (V x))
  have hroot (x : Ω) : T x ≤ Real.sqrt (A x)*Real.sqrt (B x) := by
    rw [← Real.sqrt_mul (hA0 x)]
    exact Real.le_sqrt_of_sq_le (hsq x)
  have hint : ‖∫ x, S x ∂μ‖ ≤ ∫ x, Real.sqrt (A x)*Real.sqrt (B x) ∂μ := by
    apply (norm_integral_le_integral_norm _).trans
    apply (integral_mono
      (hS.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hnorm).trans
    exact integral_mono (hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((hA.sqrt.mul hB.sqrt).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hroot
  have hcs := compact_integral_cauchy_sq (μ:=μ) hA.sqrt hB.sqrt
    (fun x => Real.sqrt_nonneg _) (fun x => Real.sqrt_nonneg _)
  simp_rw [Real.sq_sqrt (hA0 _),Real.sq_sqrt (hB0 _)] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hint 2).trans hcs

end Compact
end WaringSiegel.WSL3Poisson
