import Waring.EndgameCompletionProductScale

/-! # Polynomial cutoffs compatible with every product-box error -/

noncomputable section
open Filter
open scoped Topology
namespace Waring.EndgameCompletion

theorem powerCutoff_tendsto {κ : ℝ} (hκ : 0<κ) (P : ℕ→ℝ)
    (hP : Tendsto P atTop atTop) : Tendsto (fun n=>powerCutoff κ (P n)) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hκ).comp hP)

theorem powerCutoff_ratio_tendsto (a : ℕ) {κ b : ℝ} (hab : κ*a<b)
    (P : ℕ→ℝ) (hP : Tendsto P atTop atTop) :
    Tendsto (fun n=>(powerCutoff κ (P n) : ℝ)^a/(P n)^b) atTop (𝓝 0) := by
  have ht : Tendsto (fun n=>(P n)^(κ*a-b)) atTop (𝓝 0) := by
    simpa only [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp hP
  apply squeeze_zero' _ _ ht
  · filter_upwards [hP.eventually_ge_atTop 1] with n hn
    exact div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (by linarith) _)
  filter_upwards [hP.eventually_ge_atTop 1] with n hn
  have hp : 0<P n := zero_lt_one.trans_le hn
  calc
    _ ≤ ((P n)^κ)^a/(P n)^b := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hp.le _)) a)
      (Real.rpow_nonneg hp.le _)
    _ = _ := by rw [← Real.rpow_mul_natCast hp.le,← Real.rpow_sub hp]

theorem powerCutoff_eventually_power_bound (C : ℝ) (a : ℕ) {κ b : ℝ} (hab : κ*a<b)
    (P : ℕ→ℝ) (hP : Tendsto P atTop atTop) :
    ∀ᶠ n in atTop,C*(powerCutoff κ (P n) : ℝ)^a≤(P n)^b := by
  have hr := powerCutoff_ratio_tendsto a hab P hP
  have hc : Tendsto (fun n=>C*((powerCutoff κ (P n) : ℝ)^a/(P n)^b)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hr
  have he := hc.eventually_lt_const (by norm_num : (0 : ℝ)<1)
  filter_upwards [hP.eventually_ge_atTop 1,he] with n hn he
  rw [← mul_div_assoc] at he
  exact ((div_lt_one (Real.rpow_pos_of_pos (zero_lt_one.trans_le hn) _)).mp he).le

def productCutoffExponent (L : ℕ) : ℝ := 1/(100*(L : ℝ))

theorem productCutoffExponent_facts (L : ℕ) (hL : 0<L) :
    0<productCutoffExponent L ∧ productCutoffExponent L≤1 ∧
      productCutoffExponent L*2<1 ∧ productCutoffExponent L*3<1 ∧
        productCutoffExponent L*5<1/(L : ℝ) := by
  have hL0 : (0 : ℝ)<L := by exact_mod_cast hL
  have hL1 : (1 : ℝ)≤L := by exact_mod_cast hL
  have hb : productCutoffExponent L≤1/100 := by
    unfold productCutoffExponent
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hc : productCutoffExponent L*(L : ℝ)=1/100 := by
    unfold productCutoffExponent
    field_simp
  refine ⟨by unfold productCutoffExponent; positivity,by linarith,by linarith,by linarith,?_⟩
  apply (mul_lt_mul_right hL0).mp
  rw [one_div_mul_cancel hL0.ne']
  nlinarith [hc]

def productScaleCutoff (k L n : ℕ) : ℕ :=
  powerCutoff (productCutoffExponent L) (productScaleP k L n)

theorem productScaleP_root (k L n : ℕ) (hL : 0<L) :
    (productScaleP k L n)^(1/(L : ℝ))=(productScaleM k L n : ℝ) := by
  have hL0 : (L : ℝ)≠0 := by exact_mod_cast hL.ne'
  rw [productScaleP,← Real.rpow_natCast_mul (Nat.cast_nonneg _),mul_one_div_cancel hL0,Real.rpow_one]

theorem productScaleCutoff_tendsto (k L : ℕ) (hk : 0<k) (hL : 0<L) :
    Tendsto (productScaleCutoff k L) atTop atTop :=
  powerCutoff_tendsto (productCutoffExponent_facts L hL).1 _ (productScaleP_tendsto k L hk hL)

theorem productScaleCutoff_geometry (k L : ℕ) (hk : 0<k) (hL : 0<L) :
    ∀ᶠ n in atTop,1≤productScaleM k L n ∧ 1≤productScaleCutoff k L n ∧
      2*(k : ℝ)*(productScaleCutoff k L n : ℝ)^2≤productScaleP k L n ∧
      4*(productScaleCutoff k L n : ℝ)^3≤(productScaleP k L n)^k := by
  have hf := productCutoffExponent_facts L hL
  have hP := productScaleP_tendsto k L hk hL
  have htwo := powerCutoff_eventually_power_bound (2*(k : ℝ)) 2 hf.2.2.1 _ hP
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hthree := powerCutoff_eventually_power_bound 4 3
    (hf.2.2.2.1.trans_le hkR) _ hP
  filter_upwards [(productScaleM_tendsto k L hk hL).eventually_ge_atTop 1,
    (productScaleCutoff_tendsto k L hk hL).eventually_ge_atTop 1,htwo,hthree] with n hm hn htwo hthree
  refine ⟨hm,hn,?_,?_⟩
  · simpa only [Real.rpow_one,productScaleCutoff] using htwo
  · simpa only [Real.rpow_natCast,productScaleCutoff] using hthree

theorem productScaleCutoff_error_tendsto (k L : ℕ) (hk : 0<k) (hL : 0<L) :
    Tendsto (fun n=>(productScaleCutoff k L n : ℝ)^5/(productScaleM k L n : ℝ))
      atTop (𝓝 0) := by
  have hh := powerCutoff_ratio_tendsto 5 (productCutoffExponent_facts L hL).2.2.2.2
    (productScaleP k L) (productScaleP_tendsto k L hk hL)
  simpa only [productScaleP_root k L _ hL,productScaleCutoff] using hh

#print axioms productScaleCutoff_geometry
#print axioms productScaleCutoff_error_tendsto
end Waring.EndgameCompletion
