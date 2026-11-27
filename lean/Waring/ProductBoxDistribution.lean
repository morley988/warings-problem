import Waring.ProductBoxPositiveAverage

/-! # Literal probability distributions underlying the mixed singular integral -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

abbrev MixedSpace (u v L : ℕ) := (Fin u → ℝ)×(Fin v → Fin L → ℝ)

def productBlocksMeasure (v L : ℕ) : Measure (Fin v → Fin L → ℝ) :=
  Measure.pi (fun _ => boxMeasure L)

instance (v L : ℕ) : IsProbabilityMeasure (productBlocksMeasure v L) := by
  unfold productBlocksMeasure
  infer_instance

def mixedMeasure (u v L : ℕ) : Measure (MixedSpace u v L) :=
  (boxMeasure u).prod (productBlocksMeasure v L)

instance (u v L : ℕ) : IsProbabilityMeasure (mixedMeasure u v L) := by
  unfold mixedMeasure
  infer_instance

def mixedValue (k u v L : ℕ) (z : MixedSpace u v L) : ℝ :=
  (∑ i,z.1 i^k)+∑ j,(∏ i,z.2 j i)^k

theorem continuous_mixedValue (k u v L : ℕ) : Continuous (mixedValue k u v L) := by
  unfold mixedValue
  fun_prop

theorem e_fin_sum {s : ℕ} (f : Fin s → ℝ) : e (∑ i,f i)=∏ i,e (f i) := by
  simpa using (prod_e Finset.univ f).symm

theorem integral_unit_monomial (k : ℕ) (β : ℝ) :
    (∫ t,e (β*t^k) ∂unitIntervalMeasure)=monomialIntegral k 1 β := by
  unfold unitIntervalMeasure monomialIntegral
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one]

theorem integral_ordinary_distribution (k u : ℕ) (β : ℝ) :
    (∫ x,e (β*∑ i,x i^k) ∂boxMeasure u)=monomialIntegral k 1 β^u := by
  have he (x : Fin u → ℝ) : e (β*∑ i,x i^k)=∏ i,e (β*x i^k) := by
    rw [Finset.mul_sum,e_fin_sum]
  simp_rw [he]
  rw [boxMeasure,integral_fintype_prod_eq_pow (fun t : ℝ => e (β*t^k)),Fintype.card_fin]
  rw [integral_unit_monomial]

theorem integral_product_distribution (k v L : ℕ) (β : ℝ) :
    (∫ y,e (β*∑ j,(∏ i,y j i)^k) ∂productBlocksMeasure v L)=
      productIntegral k L 1 β^v := by
  have he (y : Fin v → Fin L → ℝ) :
      e (β*∑ j,(∏ i,y j i)^k)=∏ j,productPhase k L β (y j) := by
    rw [Finset.mul_sum,e_fin_sum]
    rfl
  simp_rw [he]
  rw [productBlocksMeasure,integral_fintype_prod_eq_pow,Fintype.card_fin,
    integral_boxMeasure_eq L _ (continuous_productPhase k L β)]
  · rfl
  · intro x
    exact (norm_e _).le

theorem mixed_characteristic (k u v L : ℕ) (β : ℝ) :
    (∫ z,e (β*mixedValue k u v L z) ∂mixedMeasure u v L)=mixedKernel k u v L β := by
  simp_rw [mixedValue,mul_add,e_add]
  rw [mixedMeasure,integral_prod_mul
    (fun x : Fin u → ℝ => e (β*∑ i,x i^k))
    (fun y : Fin v → Fin L → ℝ => e (β*∑ j,(∏ i,y j i)^k)),integral_ordinary_distribution,
    integral_product_distribution]
  rfl

theorem centered_mixed_characteristic (k u v L : ℕ) (θ β : ℝ) :
    centeredAverage (mixedMeasure u v L) (mixedValue k u v L) θ β=
      mixedKernel k u v L β*e (-β*θ) := by
  unfold centeredAverage
  have he (z : MixedSpace u v L) :
      e (β*(mixedValue k u v L z-θ))=e (β*mixedValue k u v L z)*e (-β*θ) := by
    rw [← e_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_mul_const,mixed_characteristic]

theorem centered_extended_characteristic (k u v L : ℕ) (θ β : ℝ) :
    centeredAverage ((mixedMeasure u v L).prod unitIntervalMeasure)
      (fun z : MixedSpace u v L×ℝ => z.2^k+mixedValue k u v L z.1) θ β=
      mixedKernel k (u+1) v L β*e (-β*θ) := by
  unfold centeredAverage
  have he (z : MixedSpace u v L×ℝ) :
      e (β*(z.2^k+mixedValue k u v L z.1-θ))=
        (e (β*mixedValue k u v L z.1)*e (β*z.2^k))*e (-β*θ) := by
    rw [← e_add,← e_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_mul_const,integral_prod_mul
    (fun x : MixedSpace u v L => e (β*mixedValue k u v L x))
    (fun t : ℝ => e (β*t^k)),mixed_characteristic,integral_unit_monomial]
  change (mixedKernel k u v L β*monomialIntegral k 1 β)*e (-β*θ)=_
  simp only [mixedKernel,pow_succ]
  ring

theorem integrable_centered_extended {k u v L : ℕ} (hk : 1≤k)
    (hgap : (k : ℝ)<(u+1 : ℕ)+(v : ℝ)/2) (θ : ℝ) :
    Integrable (centeredAverage ((mixedMeasure u v (L+1)).prod unitIntervalMeasure)
      (fun z : MixedSpace u v (L+1)×ℝ => z.2^k+mixedValue k u v (L+1) z.1) θ) := by
  have he := funext (centered_extended_characteristic k u v (L+1) θ)
  rw [he]
  apply (integrable_mixedKernel k (u+1) v L hk hgap).norm.mono'
  · exact ((continuous_mixedKernel k (u+1) v (L+1)).mul
      (by unfold e; fun_prop)).aestronglyMeasurable
  · filter_upwards with β
    rw [norm_mul,norm_e,mul_one]

#print axioms centered_extended_characteristic
#print axioms integrable_centered_extended
end Waring.ProductBox
