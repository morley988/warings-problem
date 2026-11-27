import WaringSiegel.WSL4KappaIdealShift

/-! # Good local kappa weights under a three-step conductor loss -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open WSL4Local

theorem cubicKappaLocal_good_antitone (q C : ℝ) (hq : 1≤q) :
    Antitone (cubicKappaLocal q C true) := by
  apply antitone_nat_of_succ_le
  intro e
  simp only [cubicKappaLocal,if_true]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hq
  have hd : ((e/3:ℕ):ℝ)≤(((e+1)/3:ℕ):ℝ) := by
    exact_mod_cast (show e/3≤(e+1)/3 by omega)
  by_cases h0 : e%3=0 <;> by_cases h1 : (e+1)%3=0
  · omega
  · simp only [h0,h1,if_true,if_false]
    linarith
  · have hd' : ((e/3:ℕ):ℝ)+1≤(((e+1)/3:ℕ):ℝ) := by
      exact_mod_cast (show e/3+1≤(e+1)/3 by omega)
    simp only [h0,h1,if_true,if_false]
    linarith
  · simp only [h0,h1,if_true,if_false]
    linarith

theorem cubicKappaAt_good_antitone (q C : ℝ) (hq : 4≤q) :
    Antitone (cubicKappaAt q C true) := by
  apply antitone_nat_of_succ_le
  intro e
  by_cases he : e=0
  · subst e
    simp only [cubicKappaAt,cubicKappaLocal,Nat.zero_add,one_ne_zero,if_false,if_true,Nat.sub_self,
      Nat.zero_div,Nat.zero_mod,Nat.cast_zero,neg_zero,zero_sub]
    have hp : q^(-(1/2:ℝ))≤(4:ℝ)^(-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)
    have hfour : (4:ℝ)^(-(1/2:ℝ))=1/2 := by
      rw [Real.rpow_neg (by norm_num),← Real.sqrt_eq_rpow]
      have hs : Real.sqrt (4:ℝ)=2 := by
        convert Real.sqrt_sq (by norm_num : (0:ℝ)≤2) using 1 <;> norm_num
      rw [hs]
      norm_num
    rw [hfour] at hp
    linarith
  · simp only [cubicKappaAt,he,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel]
    exact cubicKappaLocal_good_antitone q C (by linarith) (by omega)

theorem cubicKappaAt_good_three_step_loss (q C : ℝ) (hq : 0<q) (e : ℕ) :
    cubicKappaAt q C true e≤q*cubicKappaAt q C true (e+3) := by
  by_cases he : e=0
  · subst e
    norm_num only [cubicKappaAt,cubicKappaLocal,if_true,if_false,Nat.reduceEqDiff,
      Nat.reduceSub,Nat.reduceDiv,Nat.reduceMod,Nat.cast_zero,neg_zero,zero_sub]
    rw [Real.rpow_neg_one,mul_left_comm,mul_inv_cancel₀ hq.ne']
    norm_num
  · have he3 : e+3≠0 := by omega
    have hd : e+3-1=(e-1)+3 := by omega
    simp only [cubicKappaAt,he,he3,if_false,hd]
    rw [cubicKappaLocal_add_three q C true (e-1) hq,Real.rpow_neg_one,
      ← mul_assoc,mul_inv_cancel₀ hq.ne',one_mul]

theorem cubicKappaAt_good_cube_loss (q C : ℝ) (hq : 4≤q)
    (e f t : ℕ) (het : e≤f+3*t) :
    cubicKappaAt q C true f≤q^t*cubicKappaAt q C true e := by
  have hq0 : 0<q := by linarith
  have hstep : ∀t : ℕ,cubicKappaAt q C true f≤q^t*cubicKappaAt q C true (f+3*t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      apply ih.trans
      calc
        _ ≤ q^t*(q*cubicKappaAt q C true ((f+3*t)+3)) :=
          mul_le_mul_of_nonneg_left (cubicKappaAt_good_three_step_loss q C hq0 _) (pow_nonneg hq0.le _)
        _ = _ := by rw [pow_succ,show f+3*(t+1)=f+3*t+3 by omega]; ring
  exact (hstep t).trans (mul_le_mul_of_nonneg_left
    (cubicKappaAt_good_antitone q C hq het) (pow_nonneg hq0.le _))
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.cubicKappaAt_good_cube_loss
