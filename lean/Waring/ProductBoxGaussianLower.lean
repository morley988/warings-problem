import Waring.ProductBoxGaussianAverage

/-! # A uniform positive Gaussian contribution from one ordinary variable -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox

def gaussianMass (T h : ℝ) : ℝ :=
  T*Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2*T^2*h^2)

def monomialGaussianConstant (k : ℕ) : ℝ :=
  Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2)/(k : ℝ)

theorem monomialGaussianConstant_pos {k : ℕ} (hk : 0<k) : 0<monomialGaussianConstant k := by
  unfold monomialGaussianConstant
  exact div_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.exp_pos _)) (by exact_mod_cast hk)

theorem gaussianMass_nonneg {T : ℝ} (hT : 0≤T) (h : ℝ) : 0≤gaussianMass T h := by
  unfold gaussianMass
  positivity

theorem continuous_gaussianMass (T : ℝ) : Continuous (gaussianMass T) := by
  unfold gaussianMass
  fun_prop

theorem power_unit_lipschitz (k : ℕ) {x y : ℝ} (hx : x ∈ Set.Icc 0 1)
    (hy : y ∈ Set.Icc 0 1) : |x^k-y^k|≤(k : ℝ)*|x-y| := by
  calc
    _ ≤ |x-y| *(k : ℝ)*(max |x| |y|)^(k-1) := abs_pow_sub_pow_le x y k
    _ ≤ |x-y| *(k : ℝ)*1^(k-1) := by
      gcongr
      exact max_le (by simpa only [abs_of_nonneg hx.1] using hx.2)
        (by simpa only [abs_of_nonneg hy.1] using hy.2)
    _ = _ := by simp; ring

theorem gaussian_monomial_interval_lower {k : ℕ} (hk : 0<k) {T r : ℝ}
    (hT : 0<T) (hr : 0≤r) (hroom : r+1/((k : ℝ)*T)≤1) :
    monomialGaussianConstant k≤
      ∫ t in Set.Icc (0 : ℝ) 1,gaussianMass T (t^k-r^k) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast hk
  let δ : ℝ := 1/((k : ℝ)*T)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hr1 : r≤1 := by dsimp [δ] at hδ; linarith
  let F : ℝ → ℝ := fun t => gaussianMass T (t^k-r^k)
  have hFc : Continuous F := (continuous_gaussianMass T).comp ((continuous_id.pow k).sub continuous_const)
  have hsub : Set.Icc r (r+δ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hr.trans ht.1,ht.2.trans hroom⟩
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc r (r+δ)) :
      T*Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2)≤F t := by
    have hdiff : |t^k-r^k|≤(k : ℝ)*δ := by
      apply (power_unit_lipschitz k (hsub ht) ⟨hr,hr1⟩).trans
      apply mul_le_mul_of_nonneg_left _ hkpos.le
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]
    have hscaled : |T*(t^k-r^k)|≤1 := by
      rw [abs_mul,abs_of_pos hT]
      have hh := mul_le_mul_of_nonneg_left hdiff hT.le
      convert hh using 1
      dsimp [δ]
      field_simp
    have hsq : (T*(t^k-r^k))^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hscaled
    have hexp : -Real.pi^2≤-Real.pi^2*T^2*(t^k-r^k)^2 := by
      have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg Real.pi)
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
  have hsmall := setIntegral_ge_of_const_le (μ := (volume : Measure ℝ)) measurableSet_Icc
    measure_Icc_lt_top.ne hpoint hFc.integrableOn_Icc
  have he : (T*Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2))*
      volume.real (Set.Icc r (r+δ))=monomialGaussianConstant k := by
    rw [Real.volume_real_Icc]
    simp only [add_sub_cancel_left,max_eq_left hδ.le]
    dsimp [δ,monomialGaussianConstant]
    field_simp
  rw [he] at hsmall
  exact hsmall.trans (setIntegral_mono_set hFc.integrableOn_Icc
    (Filter.Eventually.of_forall (fun t => gaussianMass_nonneg hT.le _))
    (Filter.Eventually.of_forall hsub))

/-- Uniformity holds for every target in a fixed compact subinterval below1. -/
theorem gaussian_monomial_uniform {k : ℕ} (hk : 0<k) {b : ℝ}
    (hb0 : 0≤b) (hb1 : b<1) :
    ∃ T0 : ℝ,0<T0 ∧ ∀ T : ℝ,T0≤T → ∀ w∈Set.Icc 0 b,
      monomialGaussianConstant k≤∫ t in Set.Icc (0 : ℝ) 1,gaussianMass T (t^k-w) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast hk
  let rmax := b^((k : ℝ)⁻¹)
  have hrmax : rmax<1 := Real.rpow_lt_one hb0 hb1 (inv_pos.mpr hkpos)
  let T0 := 1/((k : ℝ)*(1-rmax))+1
  have hgap : 0<1-rmax := sub_pos.mpr hrmax
  have hT0 : 0<T0 := by dsimp [T0]; positivity
  refine ⟨T0,hT0,?_⟩
  intro T hT w hw
  have hTp : 0<T := hT0.trans_le hT
  let r := w^((k : ℝ)⁻¹)
  have hr0 : 0≤r := Real.rpow_nonneg hw.1 _
  have hrmaxle : r≤rmax := Real.rpow_le_rpow hw.1 hw.2 (inv_nonneg.mpr hkpos.le)
  have hrpow : r^k=w := Real.rpow_inv_natCast_pow hw.1 hk.ne'
  have hwidth : 1/((k : ℝ)*T)≤1-rmax := by
    apply (div_le_iff₀ (mul_pos hkpos hTp)).mpr
    have hbase : 1/((k : ℝ)*(1-rmax))≤T := by dsimp [T0] at hT; linarith
    have hh := (div_le_iff₀ (mul_pos hkpos hgap)).mp hbase
    nlinarith
  have hroom : r+1/((k : ℝ)*T)≤1 := by linarith
  simpa only [hrpow] using gaussian_monomial_interval_lower hk hTp hr0 hroom

#print axioms gaussian_monomial_uniform
end Waring.ProductBox
