import WaringLinear.EfficientDifferencing
import WaringEnvelope.ShorteningRanges

/-! The exact seed order for efficient differencing over a number field.
The gain already present in the initial defect k−1 pays the exponentially
small loss in the recurrence up to every scheduled seed. -/
noncomputable section
namespace WaringLinear
open WaringEnvelope (evenOrder seedDefect seedOrder T)
set_option maxHeartbeats 600000

private theorem log_one_sub_quadratic (x : ℝ) (hx : 0≤x) (h1 : x<1) :
    Real.log (1-x) ≤ -x-x^2/4 := by
  let y := Real.sqrt (1-x)
  have hy : 0<y := Real.sqrt_pos.mpr (by linarith)
  have he : y^2=1-x := Real.sq_sqrt (by linarith)
  have hy1 : y≤1 := (Real.sqrt_le_iff).2 ⟨by norm_num,by linarith⟩
  have hhalf : x/2≤1-y := by nlinarith only [he,sq_nonneg (1-y)]
  have hs := (sq_le_sq₀ (by positivity : 0≤x/2) (sub_nonneg.mpr hy1)).2 hhalf
  have hh := Real.log_le_sub_one_of_pos hy
  have hlog : Real.log (1-x)=2*Real.log y := by rw [←he,Real.log_pow];norm_num
  nlinarith only [hs,he,hh,hlog]

private theorem initial_potential_slack {k : ℕ} (hk : 2≤k) :
    (k:ℝ)*Real.log ((k:ℝ)-1)+((k:ℝ)-1) ≤
      k*Real.log k+k-2-1/(4*(k:ℝ)) := by
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hp : 0<(k:ℝ) := by linarith
  have h1 : (1:ℝ)/k<1 := (div_lt_one hp).2 (by linarith)
  have h := log_one_sub_quadratic (1/(k:ℝ)) (by positivity) h1
  have hm := mul_le_mul_of_nonneg_left h hp.le
  have hcoef : (k:ℝ)*(-(1/k)-(1/k)^2/4) = -1-1/(4*(k:ℝ)) := by field_simp
  rw [hcoef] at hm
  have he : (k:ℝ)-1=k*(1-1/(k:ℝ)) := by field_simp
  rw [he,Real.log_mul hp.ne' (by linarith : 1-1/(k:ℝ)≠0)]
  linarith only [hm,he]

private theorem dyadic_dominates {k : ℕ} (hk : 21≤k) : 84*k^2≤2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc
      84*(k+1)^2 ≤ 84*k^2*2 := by nlinarith [Nat.mul_le_mul_right k hk]
      _ ≤ 2^k*2 := Nat.mul_le_mul_right 2 ih
      _ = _ := by rw [pow_succ]

/-- The original k−1 defect compensates the full dyadic loss up to
order 21k. The right side is the smooth Waring seed potential. -/
theorem edDefect_wooley_potential {k r j : ℕ} (hk : 21≤k) (hr : r=2*(j+1))
    (hR : r≤21*k) :
    (k:ℝ)*Real.log (edDefect k j)+edDefect k j ≤ k*Real.log k+k-r := by
  have hk2 : 2≤k := by omega
  have hp : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hpow : 84*(k:ℝ)^2≤(2:ℝ)^k := by exact_mod_cast dyadic_dominates hk
  have hr' : (r:ℝ)≤21*k := by exact_mod_cast hR
  have hpos : 0<(2:ℝ)^k := by positivity
  have hsmall : (r:ℝ)*(1/2:ℝ)^k≤1/(4*(k:ℝ)) := by
    rw [one_div_pow,mul_one_div]
    apply (div_le_div_iff₀ hpos (by positivity)).2
    have hx := mul_le_mul_of_nonneg_right hr' (by positivity : 0≤4*(k:ℝ))
    nlinarith only [hpow,hx]
  have hr'' : (r:ℝ)=2*((j:ℝ)+1) := by exact_mod_cast hr
  have hpaid := (mul_le_mul_of_nonneg_right (show 2*(j:ℝ)≤r by linarith only [hr''])
    (by positivity : 0≤(1/2:ℝ)^k)).trans hsmall
  have h := edDefect_potential_exact_initial hk2 j
  have hinit := initial_potential_slack hk2
  linarith only [h,hinit,hpaid,hr'']

def edSeedIndex (k z : ℕ) : ℕ := ⌈((k:ℝ)*seedOrder z)/2⌉₊-1

/-- The exact rounded seed from the conductor menu is already supplied
by the numerical efficient-differencing recurrence, with no extra pair. -/
theorem edDefect_at_exact_seed (k z : ℕ) (hk : 21≤k) (hlo : T≤20*z) (hhi : 3*z≤T) :
    2*(edSeedIndex k z+1)=evenOrder (k*seedOrder z) ∧
      edDefect k (edSeedIndex k z)≤(k:ℝ)*seedDefect z := by
  let r := evenOrder (k*seedOrder z)
  have hh : 2*z≤T := by omega
  obtain ⟨h₀,_,hseed,_,hv⟩ := WaringEnvelope.seed_range z hlo hh
  have hd0 : (1:ℝ)/20≤seedDefect z := h₀.trans hseed
  have hd : 0<seedDefect z := by linarith only [hd0]
  have hinv : (seedDefect z)⁻¹≤20 := by
    rw [←one_div];apply (div_le_iff₀ hd).2;linarith only [hd0]
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hlog
  have hmax : seedOrder z≤20 := by unfold seedOrder;linarith only [hlog,hinv,hd]
  have hp : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hk2 : (2:ℝ)≤k := by exact_mod_cast (show 2≤k by omega)
  have hbudget := WaringEnvelope.evenOrder_bounds ((k:ℝ)*seedOrder z) (mul_nonneg hp.le hv)
  change (k:ℝ)*seedOrder z≤r ∧ (r:ℝ)<k*seedOrder z+2 at hbudget
  have hrpos : 0<r := (show 0<k by omega).trans_le
    (WaringEnvelope.guarded_seed (P:=fun _ _ => True) (k:=k) hlo hhi True.intro).1
  have hindex : r=2*(edSeedIndex k z+1) := by
    dsimp [r,evenOrder,edSeedIndex] at hrpos ⊢
    omega
  have hupper : r≤21*k := by
    have hh' := mul_le_mul_of_nonneg_left hmax hp.le
    have hr' : (r:ℝ)≤21*k := by linarith only [hh',hbudget.2,hk2]
    exact_mod_cast hr'
  refine ⟨hindex.symm,?_⟩
  have hpot := edDefect_wooley_potential hk hindex hupper
  by_contra! hbad
  have hlog' := Real.log_lt_log (mul_pos hp hd) hbad
  rw [Real.log_mul hp.ne' hd.ne'] at hlog'
  have hcompare := add_lt_add (mul_lt_mul_of_pos_left hlog' hp) hbad
  unfold seedOrder at hbudget
  linarith only [hcompare,hpot,hbudget.1]

#print axioms edDefect_wooley_potential
#print axioms edDefect_at_exact_seed
end WaringLinear
