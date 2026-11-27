import Waring.ProductBoxArcError

/-! # Exact factorization of the finite narrow-major model -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion RestrictedSmoothArcs

theorem modelArcIntegral_unit_sum (k u v L M n : ℕ) (hkuv : k≤u+v)
    (hM : 0<M) (q : ℕ+) (N : ℝ) :
    (∑ a : (ZMod (q : ℕ))ˣ,modelArcIntegral k u v L M n (N/((M : ℝ)^L)^k) ⟨q,a⟩)=
      productSingularCoefficient k u v L (n : ℤ) q*
        (((M : ℝ)^L : ℝ) : ℂ)^(u+v-k)*
          ∫ γ in -N..N,singularIntegrand k u v L ((n : ℝ)/((M : ℝ)^L)^k) γ := by
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  unfold modelArcIntegral
  rw [← intervalIntegral.integral_finset_sum
    (fun a _ => (continuous_modelArcIntegrand k u v L M n ⟨q,a⟩).intervalIntegrable _ _)]
  have he (β : ℝ) : (∑ a : (ZMod (q : ℕ))ˣ,modelArcIntegrand k u v L M n ⟨q,a⟩ β)=
      productSingularCoefficient k u v L (n : ℤ) q*mixedOscillatory k u v L M n β := by
    simpa only [modelArcIntegrand,arcLabelRat_real] using
      sum_mixedMajorModel_factor k u v L M q n β
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,mixedOscillatory_integral_scale k u v L hkuv hMr]
  ring

theorem modelArcIntegral_sum (k u v L M n : ℕ) (hkuv : k≤u+v)
    (hM : 0<M) (S : Finset ℕ+) (N : ℝ) :
    (∑ p∈denominatorArcLabels S,modelArcIntegral k u v L M n (N/((M : ℝ)^L)^k) p)=
      (∑ q∈S,productSingularCoefficient k u v L (n : ℤ) q)*
        (((M : ℝ)^L : ℝ) : ℂ)^(u+v-k)*
          ∫ γ in -N..N,singularIntegrand k u v L ((n : ℝ)/((M : ℝ)^L)^k) γ := by
  simp only [denominatorArcLabels,Finset.sum_sigma,
    modelArcIntegral_unit_sum k u v L M n hkuv hM]
  rw [← Finset.sum_mul,← Finset.sum_mul]

#print axioms modelArcIntegral_sum
end Waring.ProductBox
