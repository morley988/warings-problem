import WaringEnvelope.RealCosts
import WaringEnvelope.TailMonotonicity
import Mathlib.Analysis.Complex.Exponential

/-! # Real price of the last conductor band

The finite plateau, the infinite Weyl tail, clipping at √k/8, and rounding
the final number of variables are charged at the actual degree k. The
terminal guard only needs to check the left endpoint of the band.
-/

noncomputable section

namespace WaringEnvelope

private theorem infinite_scaled_ceil (a b : ℕ) (hb : 0<b) :
    (a:ℝ)/b/D ≤ (ceilDiv a b : ℝ)/D := by
  exact div_le_div_of_nonneg_right (real_le_ceilDiv a b hb) (by positivity)

/-- A single successful integer terminal test bounds the actual real price
at every degree of the infinite band. The logarithmic cap correction has
its argument and its square root evaluated at that degree. -/
theorem infiniteFinal_real_price (c : Config) (s : State) (z₀ bound k : ℕ) (R : ℝ)
    (hk : c.first ≤ k) (hR : R ≤ (s.cost : ℝ)/D)
    (hbase : validLog (T-z₀) z₀ c.baseLog = true)
    (hend : validLog c.first 1 c.endLog = true)
    (hf : infiniteFinal c s bound = true) :
    2 + Real.log (((T-z₀ : ℕ) : ℝ)/z₀) + R +
      2*V/(F*U)*Real.log ((s.height:ℝ)*14*F^2/T) + 4*V/(F*U) +
      16*V/U*(Real.log ((64*V/(14*U):ℝ)*(Real.log k+81/10))/Real.sqrt k) +
      16/Real.sqrt k + 6/k < (bound:ℝ)/D := by
  simp only [infiniteFinal, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hf
  obtain ⟨_,hsq,hlarge,_,_,_,hplateau,_,hcap,hbudget⟩ := hf
  let XN := 64*V*(10*c.endLog+81*D)
  let XD := 14*U*10*D
  change validLog XN XD c.capLog = true at hcap
  have hD : (0:ℝ)<D := by norm_num [D]
  have hU : (0:ℝ)<U := by norm_num [U]
  have hV : (0:ℝ)<V := by norm_num [V]
  have hF : (0:ℝ)<F := by norm_num [F]
  have hc : 0<c.first := (by decide : 0 < 10^8).trans_le hlarge
  have hr : 0<c.root := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hc.ne'
    simpa [hz] using hsq
  have hK : 0<(c.first:ℝ) := by exact_mod_cast hc
  have hr' : 0<(c.root:ℝ) := by exact_mod_cast hr
  have hKr : 1≤(c.first:ℝ) := by exact_mod_cast (show 1 ≤ c.first from hc)
  have hkk : (c.first:ℝ)≤k := by exact_mod_cast hk
  have hsqrt : Real.sqrt (c.first:ℝ) = c.root := by
    rw [hsq, Nat.cast_pow, Real.sqrt_sq (by positivity)]
  have hrootmono := Real.sqrt_le_sqrt hkk
  rw [hsqrt] at hrootmono
  let A : ℝ := 64*V/(14*U)
  have hA : 1≤A := by norm_num [A,U,V]
  have hAp : 0<A := zero_lt_one.trans_le hA
  have hLg : Real.log (c.first:ℝ) ≤ (c.endLog:ℝ)/D := by
    simpa using validLog_sound _ _ _ hend
  have hArg : 0 < Real.log (c.first:ℝ)+81/10 := by linarith [Real.log_nonneg hKr]
  have hexp : Real.exp 1 ≤ A*(Real.log c.first+81/10) := by
    have hj := le_mul_of_one_le_left hArg.le hA
    have half : Real.exp (1/2:ℝ) ≤ 2 := by
      convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1) using 1
      norm_num
    have he : Real.exp 1 ≤ 4 := calc
      _ = Real.exp (1/2:ℝ)*Real.exp (1/2:ℝ) := by rw [← Real.exp_add]; norm_num
      _ ≤ 2*2 := mul_le_mul half half (Real.exp_pos _).le (by norm_num)
      _ = _ := by norm_num
    linarith [Real.log_nonneg hKr]
  have hmono := log_log_div_sqrt_antitone hKr hkk hAp (by norm_num : (2:ℝ)≤81/10) hexp
  have hquot : (XN:ℝ)/XD=A*((c.endLog:ℝ)/D+81/10) := by
    dsimp [XN,XD,A]
    push_cast
    field_simp
  have hlcap := validLog_sound _ _ _ hcap
  rw [hquot] at hlcap
  have hlK : Real.log (A*(Real.log c.first+81/10)) ≤ (c.capLog:ℝ)/D :=
    (Real.log_le_log (mul_pos hAp hArg) (mul_le_mul_of_nonneg_left
      (add_le_add_right hLg _) hAp.le)).trans hlcap
  rw [hsqrt] at hmono
  have hratio := hmono.trans (div_le_div_of_nonneg_right hlK hr'.le)
  have hpl := validLog_sound _ _ _ hplateau
  push_cast at hpl
  have hpl' := infinite_scaled_ceil (2*c.plateauLog*V) (F*U) (by decide)
  have htail := infinite_scaled_ceil (4*D*V) (F*U) (by decide)
  have hclip := infinite_scaled_ceil (16*c.capLog*V) (c.root*U)
    (Nat.mul_pos hr (by decide))
  have hrnd := infinite_scaled_ceil (16*D) c.root hr
  have hsix := infinite_scaled_ceil (6*D) c.first hc
  push_cast at hpl' htail hclip hrnd hsix
  have hpprice : 2*V/(F*U)*Real.log ((s.height:ℝ)*14*F^2/T)
      ≤ (ceilDiv (2*c.plateauLog*V) (F*U):ℝ)/D := by
    calc
      _ ≤ 2*V/(F*U)*((c.plateauLog:ℝ)/D) :=
        mul_le_mul_of_nonneg_left hpl (by positivity)
      _ ≤ _ := by convert hpl' using 1; ring
  have htprice : (4:ℝ)*V/(F*U) ≤ (ceilDiv (4*D*V) (F*U):ℝ)/D := by
    calc
      _ = 4*(D:ℝ)*V/(F*U)/D := by field_simp
      _ ≤ _ := htail
  have hcprice : (16:ℝ)*V/U*(Real.log (A*(Real.log k+81/10))/Real.sqrt k)
      ≤ (ceilDiv (16*c.capLog*V) (c.root*U):ℝ)/D := by
    calc
      _ ≤ (16:ℝ)*V/U*((c.capLog:ℝ)/D/c.root) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ _ := by convert hclip using 1; ring
  have hrprice : (16:ℝ)/Real.sqrt k ≤ (ceilDiv (16*D) c.root:ℝ)/D := by
    refine (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤16) hr' hrootmono).trans ?_
    convert hrnd using 1
    field_simp
  have hsprice : (6:ℝ)/k ≤ (ceilDiv (6*D) c.first:ℝ)/D := by
    refine (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤6) hK hkk).trans ?_
    convert hsix using 1
    field_simp
  have hraw := (div_lt_div_iff_of_pos_right hD).2 (show
    ((2*D+c.baseLog+s.cost+ceilDiv (2*c.plateauLog*V) (F*U)+
      ceilDiv (4*D*V) (F*U)+ceilDiv (16*c.capLog*V) (c.root*U)+
      ceilDiv (16*D) c.root+ceilDiv (6*D) c.first : ℕ):ℝ) < (bound:ℝ)
    by exact_mod_cast hbudget)
  push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hraw
  simp only [add_div] at hraw
  rw [show (2:ℝ)*D/D=2 by field_simp] at hraw
  have h0 := validLog_sound _ _ _ hbase
  change 2 + _ + R + _ + _ + 16*V/U*(Real.log (A*(Real.log k+81/10))/Real.sqrt k)
    + 16/Real.sqrt k + 6/k < (bound:ℝ)/D
  linarith only [hraw,h0,hR,hpprice,htprice,hcprice,hrprice,hsprice]

#print axioms infiniteFinal_real_price

end WaringEnvelope
