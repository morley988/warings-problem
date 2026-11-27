import WaringLinear.MomentAbsorption

/-! # Inserting several ordinary variables and absorbing an arbitrary defect -/
noncomputable section
open MeasureTheory
namespace WaringLinear

/-- Weighted arithmetic–geometric mean with one distinguished factor. -/
theorem distinguished_factor_bound (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (a : ℕ) :
    ((a:ℝ)+1)*x*y^a ≤ x^(a+1)+(a:ℝ)*y^(a+1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hsg : 0 ≤ (x-y)*(x^(a+1)-y^(a+1)) := by
      rcases le_total x y with h|h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr (pow_le_pow_left₀ hx h _))
      · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (pow_le_pow_left₀ hy h _))
    have hprev := mul_le_mul_of_nonneg_right ih hy
    rw [Nat.cast_succ,pow_succ x (a+1),pow_succ y (a+1)]
    simp only [pow_succ _ a] at hsg hprev ⊢
    linarith only [hsg,hprev]

variable {T : Type*} [MeasurableSpace T]

/-- An integral comparison with one ordinary factor implies the comparison
with any positive number of ordinary factors, through the full order. -/
theorem many_mixed_of_one_mixed (μ : Measure T) (F f : T → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hf : ∀ x, 0 ≤ f x) (n a : ℕ)
    (hI : Integrable (fun x => F x^(n+a+1)) μ)
    (hOne : Integrable (fun x => f x*F x^(n+a)) μ)
    (hMany : Integrable (fun x => f x^(a+1)*F x^n) μ)
    (hSupport : (∫ x, F x^(n+a+1) ∂μ) ≤ ∫ x, f x*F x^(n+a) ∂μ) :
    (∫ x, F x^(n+a+1) ∂μ) ≤ ∫ x, f x^(a+1)*F x^n ∂μ := by
  have hstep (x) : ((a:ℝ)+1)*(f x*F x^(n+a)) ≤
      f x^(a+1)*F x^n + (a:ℝ)*F x^(n+a+1) := by
    have hp := mul_le_mul_of_nonneg_right
      (distinguished_factor_bound (f x) (F x) (hf x) (hF x) a) (pow_nonneg (hF x) n)
    rw [show n+a+1=n+(a+1) by omega,pow_add (F x) n a,pow_add (F x) n (a+1)]
    linarith only [hp]
  have hb := integral_mono (hOne.const_mul ((a:ℝ)+1)) (hMany.add (hI.const_mul a)) hstep
  simp only [Pi.add_apply,integral_const_mul,integral_add hMany (hI.const_mul a)] at hb
  have hm := mul_le_mul_of_nonneg_left hSupport (by positivity : 0≤(a:ℝ)+1)
  linarith

theorem several_factor_split {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (n a : ℕ) :
    x^(a+1)*y^n ≤ (2*x)^(n+a+1)+(1/2:ℝ)*y^(n+a+1) := by
  by_cases h : y ≤ 2*x
  · have hab := mul_le_mul (pow_le_pow_left₀ hx (show x≤2*x by linarith) (a+1))
        (pow_le_pow_left₀ hy h n) (pow_nonneg hy _) (by positivity : 0≤(2*x)^(a+1))
    rw [←pow_add, show a+1+n = n+a+1 by omega] at hab
    exact hab.trans (le_add_of_nonneg_right (by positivity))
  · have hp : x ≤ y := by linarith
    have hh : x ≤ (1/2:ℝ)*y := by linarith
    have hab := mul_le_mul (pow_le_pow_left₀ hx hp a) hh hx (pow_nonneg hy a)
    have hh2 := mul_le_mul_of_nonneg_right hab (pow_nonneg hy n)
    rw [pow_succ x a,show n+a+1=n+(a+1) by omega,pow_add y n (a+1),pow_succ y a]
    nlinarith only [hh2,show 0≤(2*x)^(n+(a+1)) by positivity]

/-- Full major/minor absorption for a+1 ordinary copies and m+d restricted
copies. The major-arc term uses the full ordinary moment. -/
theorem absorb_several_mixed (μ : Measure T) (M : Set T) (hM : MeasurableSet M)
    (F f : T → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hf0 : ∀ x, 0 ≤ f x)
    (m d a : ℕ) (P B : ℝ) (hB : 0 ≤ B)
    (hBox : ∀ x ∈ Mᶜ, F x ≤ P) (hMinor : ∀ x ∈ Mᶜ, f x ≤ B)
    (hI : Integrable (fun x => F x^(m+d+a+1)) μ)
    (hJ : Integrable (fun x => f x^(m+d+a+1)) μ)
    (hr : Integrable (fun x => F x^m) μ)
    (hmix : Integrable (fun x => f x^(a+1)*F x^(m+d)) μ)
    (hSupport : (∫ x, F x^(m+d+a+1) ∂μ) ≤ ∫ x, f x^(a+1)*F x^(m+d) ∂μ) :
    (∫ x, F x^(m+d+a+1) ∂μ) ≤
      2*((2:ℝ)^(m+d+a+1)*(∫ x in M, f x^(m+d+a+1) ∂μ) +
        B^(a+1)*P^d*(∫ x in Mᶜ, F x^m ∂μ)) := by
  have hMajor : (∫ x in M, f x^(a+1)*F x^(m+d) ∂μ) ≤
      (2:ℝ)^(m+d+a+1)*(∫ x in M, f x^(m+d+a+1) ∂μ)+
      (1/2:ℝ)*(∫ x in M, F x^(m+d+a+1) ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
    · apply setIntegral_mono_on hmix.integrableOn
        (((hJ.const_mul _).add (hI.const_mul _)).integrableOn) hM
      intro x _
      simpa only [mul_pow] using several_factor_split (hf0 x) (hF0 x) (m+d) a
    · exact (hJ.const_mul _).integrableOn
    · exact (hI.const_mul _).integrableOn
  have hMinorBound : (∫ x in Mᶜ, f x^(a+1)*F x^(m+d) ∂μ) ≤
      B^(a+1)*P^d*(∫ x in Mᶜ, F x^m ∂μ) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hmix.integrableOn (hr.const_mul _).integrableOn hM.compl
    intro x hx
    rw [pow_add]
    calc
      _ = (f x^(a+1)*F x^d)*F x^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul (pow_le_pow_left₀ (hf0 x) (hMinor x hx) (a+1))
          (pow_le_pow_left₀ (hF0 x) (hBox x hx) d)
          (pow_nonneg (hF0 x) _) (pow_nonneg hB _)) (pow_nonneg (hF0 x) _)
  have hsub : (∫ x in M, F x^(m+d+a+1) ∂μ) ≤ ∫ x, F x^(m+d+a+1) ∂μ :=
    setIntegral_le_integral hI (Filter.Eventually.of_forall (fun x => pow_nonneg (hF0 x) _))
  rw [← integral_add_compl hM hmix] at hSupport
  linarith

#print axioms many_mixed_of_one_mixed
#print axioms absorb_several_mixed
end WaringLinear
