import WaringFieldSmall.Check
import WaringLinear.EfficientDifferencing
import Mathlib.Tactic

/-! # Outward rounding of the field differencing recurrence
Each interval uses its larger degree in the denominator of the
decrement and its smaller degree in the dyadic saving. -/
noncomputable section
namespace WaringFieldSmall
open WaringLinear

private theorem subtract_cast_le (d n : ℕ) : (d:ℝ)-n≤((d-n:ℕ):ℝ) := by
  by_cases h : n≤d
  · rw [Nat.cast_sub h]
  · have h' : (d:ℝ)≤n := by exact_mod_cast le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le (le_of_not_ge h),Nat.cast_zero]
    linarith

private def clipped (hi cap d : ℝ) := d-2*d/(hi+d)*((cap-1)/cap)

private theorem clipped_mono {hi cap x y : ℝ} (hh : 2≤hi) (hc : 1≤cap)
    (hx : 0≤x) (hxy : x≤y) : clipped hi cap x≤clipped hi cap y := by
  have hp : 0<hi+x := by linarith
  have hq : 0<hi+y := by linarith
  have hcp : 0<cap := by linarith
  have hx' : 0≤y := hx.trans hxy
  have hprod : 2*hi≤(hi+y)*(hi+x) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh) (show 0≤hi by linarith),
      mul_nonneg (show 0≤hi by linarith) hx,mul_nonneg (show 0≤hi by linarith) hx',
      mul_nonneg hx hx']
  have hc1 : (cap-1)/cap≤1 := (div_le_one hcp).2 (by linarith)
  have hnum := (mul_le_mul_of_nonneg_left hc1 (by linarith : 0≤2*hi)).trans
    (by simpa only [mul_one] using hprod)
  have factor : 0≤1-(2*hi*((cap-1)/cap))/((hi+y)*(hi+x)) :=
    sub_nonneg.mpr ((div_le_one (mul_pos hq hp)).2 hnum)
  have diff : clipped hi cap y-clipped hi cap x =
      (y-x)*(1-(2*hi*((cap-1)/cap))/((hi+y)*(hi+x))) := by
    unfold clipped
    field_simp [hp.ne',hq.ne',hcp.ne']
    ring
  apply sub_nonneg.mp
  rw [diff]
  exact mul_nonneg (sub_nonneg.mpr hxy) factor

private theorem clipped_edStep {lo hi k : ℕ} {x : ℝ}
    (hl : 2≤lo) (hlo : lo≤k) (hhi : k≤hi) (hx : 0≤x) (hxk : x≤k) :
    edStep k x≤clipped hi (2^(min lo 32):ℕ) x := by
  let m := min lo 32
  let c : ℝ := 2^m
  have hk' : (2:ℝ)≤k := by exact_mod_cast hl.trans hlo
  have hhi' : (k:ℝ)≤hi := by exact_mod_cast hhi
  have hkp : 0<(k:ℝ) := by linarith
  have hden : 0<(k:ℝ)+x := by linarith
  have hhiD : 0<(hi:ℝ)+x := by linarith
  have hc : 1≤c := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hcp : 0<c := by linarith
  have hm : m≤k := (min_le_left _ _).trans hlo
  have hr : 0≤edRatio k x := div_nonneg (sub_nonneg.mpr hxk) (by positivity)
  have hratio : edRatio k x≤1/2 := by
    unfold edRatio
    apply (div_le_iff₀ (show 0<(2:ℝ)*k by positivity)).2
    linarith
  have hpow : edRatio k x^k≤1/c := by
    calc
      _ ≤ (1/2:ℝ)^k := pow_le_pow_left₀ hr hratio _
      _ ≤ (1/2:ℝ)^m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = _ := by simp only [c,one_div_pow]
  have hfrac : (c-1)/c≤1-edRatio k x^k := by
    rw [sub_div,div_self hcp.ne'];linarith
  have hdiv := div_le_div_of_nonneg_left (show 0≤2*x by positivity) hden
    (add_le_add_right hhi' x)
  have hmul := mul_le_mul hdiv hfrac (div_nonneg (by linarith) hcp.le)
    (div_nonneg (by positivity) hden.le)
  unfold edStep clipped
  push_cast
  change x-_≤x-2*x/((hi:ℝ)+x)*((c-1)/c)
  linarith only [hmul]

private theorem rounded_upper {hi cap : ℕ} (hhi : 2≤hi) (hc : 1≤cap) (d : ℕ) :
    clipped hi cap ((d:ℝ)/scale)≤(edRound hi cap d:ℝ)/scale := by
  let a := 2*d*scale*(cap-1)
  let b := (hi*scale+d)*cap
  have hp : (0:ℝ)<scale := by norm_num [scale]
  have hh : (2:ℝ)≤hi := by exact_mod_cast hhi
  have hc' : (1:ℝ)≤cap := by exact_mod_cast hc
  have hden : 0<(hi:ℝ)+(d:ℝ)/scale := by positivity
  have hq := Nat.cast_div_le (α:=ℝ) (m:=a) (n:=b)
  have he : (a:ℝ)/(b:ℝ)/scale = 2*((d:ℝ)/scale)/(hi+d/scale)*((cap-1)/cap) := by
    dsimp [a,b]
    rw [Nat.cast_mul,Nat.cast_sub hc]
    push_cast
    field_simp
  have hR := div_le_div_of_nonneg_right hq hp.le
  rw [he] at hR
  have hsub := div_le_div_of_nonneg_right (subtract_cast_le d (a/b)) hp.le
  rw [sub_div] at hsub
  change clipped hi cap ((d:ℝ)/scale)≤((d-a/b:ℕ):ℝ)/scale
  unfold clipped
  linarith only [hR,hsub]

private theorem repeats_succ (f : Nat → Nat) (n x : Nat) : repeats f (n+1) x=f (repeats f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- Every recorded starting defect bounds the exact ED recurrence at
each degree in its band. -/
theorem edDefect_le_start {lo hi k : Nat} (hl : 2≤lo) (hlo : lo≤k) (hhi : k≤hi) (j : Nat) :
    edDefect k j≤((start lo hi j).defect:ℝ)/scale := by
  let cap := 2^(min lo 32)
  have hcap : 1≤cap := Nat.one_le_pow _ _ (by decide)
  have hh : 2≤hi := hl.trans (hlo.trans hhi)
  induction j with
  | zero =>
    unfold start
    simp only [repeats,edDefect, Nat.cast_mul,Nat.cast_sub (by omega : 1≤hi),Nat.cast_one]
    have hp : (scale:ℝ)≠0 := by norm_num [scale]
    rw [mul_div_cancel_right₀ _ hp]
    exact sub_le_sub_right (by exact_mod_cast hhi) _
  | succ j ih =>
    obtain ⟨hp,hm,_⟩ := edDefect_bounds (hl.trans hlo) j
    change edStep k (edDefect k j)≤(repeats (edRound hi cap) (j+1) ((hi-1)*scale):ℝ)/scale
    rw [repeats_succ]
    exact (clipped_edStep hl hlo hhi hp.le hm).trans
      ((clipped_mono (by exact_mod_cast hh) (by exact_mod_cast hcap) hp.le ih).trans
      (rounded_upper hh hcap _))

#print axioms edDefect_le_start
end WaringFieldSmall
