import WaringLinear.SeveralFactors

/-! # Pruning a mixed annulus with a loss-free restricted moment -/
noncomputable section
open MeasureTheory
namespace WaringLinear

/-- A scaled pointwise split for two ordinary integral powers. -/
theorem scaled_factor_split (f F L : ℝ) (hf : 0≤f) (hF : 0≤F) (hL : 0<L) (a b : ℕ) :
    f^a*F^b ≤ L^b*f^(a+b) + L⁻¹^a*F^(a+b) := by
  by_cases h : F≤L*f
  · have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hF h b) (pow_nonneg hf a)
    rw [mul_pow] at hh
    rw [pow_add,pow_add]
    linarith only [hh,show 0≤L⁻¹^a*(F^a*F^b) by positivity]
  · have hh : f ≤ L⁻¹*F := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hL).2 (by linarith)
    have hb := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hf hh a) (pow_nonneg hF b)
    rw [mul_pow] at hb
    rw [pow_add,pow_add]
    linarith only [hb,show 0≤L^b*(f^a*f^b) by positivity]

/-- If the full ordinary S-th moment on an annulus saves Q^-δ and the
restricted S-th moment is loss-free, then a ordinary factors retain the exact
saving Q^(-δ a/S). The proof gives the implied constant. -/
theorem annulus_pruning {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (M : Set T) (hM : MeasurableSet M) (f F : T → ℝ)
    (hf : ∀ x, 0≤f x) (hF : ∀ x, 0≤F x) (a b : ℕ) (hS : 0<a+b)
    (hIf : Integrable (fun x => f x^(a+b)) μ)
    (hIF : Integrable (fun x => F x^(a+b)) μ)
    (hI : Integrable (fun x => f x^a*F x^b) μ)
    (Q δ A D P : ℝ) (hQ : 0<Q)
    (hOrd : (∫ x in M, f x^(a+b) ∂μ) ≤ A*P*Q^(-δ))
    (hRest : (∫ x, F x^(a+b) ∂μ) ≤ D*P) :
    (∫ x in M, f x^a*F x^b ∂μ) ≤ (A+D)*P*Q^(-δ*a/((a:ℝ)+b)) := by
  have hS' : (0:ℝ)<(a:ℝ)+b := by exact_mod_cast hS
  let L : ℝ := Q^(δ/((a:ℝ)+b))
  have hL : 0<L := Real.rpow_pos_of_pos hQ _
  have hbound : (∫ x in M, f x^a*F x^b ∂μ) ≤ L^b*(∫ x in M, f x^(a+b) ∂μ)+
      L⁻¹^a*(∫ x in M, F x^(a+b) ∂μ) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add]
    · exact setIntegral_mono_on hI.integrableOn
        (((hIf.const_mul _).add (hIF.const_mul _)).integrableOn) hM
        (fun x _ => scaled_factor_split _ _ L (hf x) (hF x) hL a b)
    · exact (hIf.const_mul _).integrableOn
    · exact (hIF.const_mul _).integrableOn
  have hfine : (∫ x in M, F x^(a+b) ∂μ) ≤ D*P :=
    (setIntegral_le_integral hIF (Filter.Eventually.of_forall
      (fun x => pow_nonneg (hF x) _))).trans hRest
  have hpow : L^b*Q^(-δ)=Q^(-δ*a/((a:ℝ)+b)) := by
    dsimp [L]
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le,← Real.rpow_add hQ]
    congr 1
    field_simp
    ring
  have hinv : L⁻¹^a=Q^(-δ*a/((a:ℝ)+b)) := by
    dsimp [L]
    rw [← Real.rpow_neg hQ.le,← Real.rpow_natCast,← Real.rpow_mul hQ.le]
    congr 1
    ring
  calc
    _ ≤ _ := hbound
    _ ≤ L^b*(A*P*Q^(-δ)) + L⁻¹^a*(D*P) := add_le_add
      (mul_le_mul_of_nonneg_left hOrd (pow_nonneg hL.le _))
      (mul_le_mul_of_nonneg_left hfine (pow_nonneg (inv_nonneg.mpr hL.le) _))
    _ = _ := by rw [hinv]; linear_combination A*P*hpow

#print axioms annulus_pruning
end WaringLinear
