import WaringSiegel.WSL3ConductorWeightedIdeal

/-! # WSL3: the manuscript's explicit cubic conductor weight

The index e denotes the positive conductor exponent e+1. This module proves
arithmetic convergence of the explicit weight. It does not assert the
remaining twisted complete-sum estimate for that weight.
-/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace WaringSiegel

def cubicKappaLocal (q C : ℝ) (good : Bool) (e : ℕ) : ℝ :=
  if good then 2*q^(-((e/3 : ℕ) : ℝ) - if e%3=0 then (1/2 : ℝ) else 1)
  else C*q^(-((e+1 : ℕ) : ℝ)/3)

def cubicKappaLocalMoment (q C : ℝ) (good : Bool) (m : ℕ) (t : ℝ) (e : ℕ) : ℝ :=
  q^(((e+1 : ℕ) : ℝ)*t) * cubicKappaLocal q C good e ^ m

theorem cubicKappaLocal_nonneg (q C : ℝ) (good : Bool) (e : ℕ)
    (hq : 0 ≤ q) (hC : 0 ≤ C) : 0 ≤ cubicKappaLocal q C good e := by
  unfold cubicKappaLocal
  split_ifs <;> positivity

theorem cubicKappaLocalMoment_nonneg (q C : ℝ) (good : Bool) (m e : ℕ) (t : ℝ)
    (hq : 0 ≤ q) (hC : 0 ≤ C) : 0 ≤ cubicKappaLocalMoment q C good m t e :=
  mul_nonneg (Real.rpow_nonneg hq _) (pow_nonneg (cubicKappaLocal_nonneg q C good e hq hC) _)

theorem cubicKappaLocal_add_three (q C : ℝ) (good : Bool) (e : ℕ) (hq : 0 < q) :
    cubicKappaLocal q C good (e+3) = q^(-1 : ℝ)*cubicKappaLocal q C good e := by
  have hd : (e+3)/3=e/3+1 := by omega
  have hm : (e+3)%3=e%3 := by omega
  unfold cubicKappaLocal
  simp only [hd,hm,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  split_ifs
  all_goals rw [mul_left_comm,← Real.rpow_add hq]
  all_goals congr 2 <;> ring

theorem cubicKappaLocalMoment_add_three (q C : ℝ) (good : Bool) (m e : ℕ) (t : ℝ)
    (hq : 0 < q) :
    cubicKappaLocalMoment q C good m t (e+3) =
      q^(3*t-(m:ℝ))*cubicKappaLocalMoment q C good m t e := by
  unfold cubicKappaLocalMoment
  rw [cubicKappaLocal_add_three q C good e hq,mul_pow,
    ← Real.rpow_mul_natCast hq.le,← mul_assoc,← Real.rpow_add hq]
  rw [← mul_assoc,← Real.rpow_add hq]
  congr 2
  push_cast
  ring

theorem cubicKappaLocalMoment_good_formula (q C : ℝ) (m e : ℕ) (t : ℝ) (hq : 0 < q) :
    cubicKappaLocalMoment q C true m t e =
      2^m*q^(((e+1 : ℕ) : ℝ)*t +
        (-((e/3 : ℕ) : ℝ) - if e%3=0 then (1/2 : ℝ) else 1)*(m:ℝ)) := by
  simp only [cubicKappaLocalMoment,cubicKappaLocal, Bool.true_eq, if_true,mul_pow]
  rw [← Real.rpow_mul_natCast hq.le,mul_left_comm,← Real.rpow_add hq]

theorem cubicKappaLocalMoment_good_initial (q C : ℝ) (m : ℕ) (t δ : ℝ)
    (hq : 2 ≤ q) (h1 : δ ≤ (m:ℝ)/2-t) (h2 : δ ≤ (m:ℝ)-2*t)
    (h3 : δ ≤ (m:ℝ)-3*t) (e : ℕ) (he : e < 3) :
    cubicKappaLocalMoment q C true m t e ≤ 2^m*q^(-δ) := by
  rw [cubicKappaLocalMoment_good_formula q C m e t (by linarith)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ q)
  interval_cases e <;> norm_num <;> linarith

theorem cubicKappaLocalMoment_good_summable_bound (q C : ℝ) (m : ℕ) (t δ : ℝ)
    (hq : 2 ≤ q) (hδ : 1 < δ) (h1 : δ ≤ (m:ℝ)/2-t)
    (h2 : δ ≤ (m:ℝ)-2*t) (h3 : δ ≤ (m:ℝ)-3*t) :
    Summable (cubicKappaLocalMoment q C true m t) ∧
      (∑' e, cubicKappaLocalMoment q C true m t e) ≤ 6*2^m*q^(-δ) := by
  have hq0 : 0 < q := by linarith
  have hr : q^(3*t-(m:ℝ)) ≤ (1/2 : ℝ) := by
    calc
      _ ≤ q^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1/q := by rw [Real.rpow_neg_one,one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by norm_num) hq
  have h := eventual_three_step_summable_bound
    (fun _ : Unit => cubicKappaLocalMoment q C true m t) 0 (2^m*q^(-δ))
    (q^(3*t-(m:ℝ))) (by positivity) (by positivity) hr
    (fun _ e => by
      unfold cubicKappaLocalMoment cubicKappaLocal
      simp only [Bool.true_eq,if_true]
      positivity)
    (fun _ e he => cubicKappaLocalMoment_good_initial q C m t δ hq h1 h2 h3 e (by simpa using he))
    (fun _ => ⟨(),fun e _ => (cubicKappaLocalMoment_add_three q C true m e t hq0).le⟩) ()
  refine ⟨h.1,?_⟩
  convert h.2 using 1 <;> norm_num <;> ring

theorem cubicKappaLocalMoment_all_summable (q C : ℝ) (good : Bool) (m : ℕ) (t : ℝ)
    (hq : 2 ≤ q) (hC : 0 ≤ C) (ht : 3*t-(m:ℝ) < -1) :
    Summable (cubicKappaLocalMoment q C good m t) := by
  let f := cubicKappaLocalMoment q C good m t
  have hf : ∀ e, 0 ≤ f e := fun e => cubicKappaLocalMoment_nonneg q C good m e t (by linarith) hC
  have hb (e : ℕ) (he : e < 3) : f e ≤ f 0+f 1+f 2 := by
    interval_cases e <;> linarith [hf 0,hf 1,hf 2]
  have hr : q^(3*t-(m:ℝ)) ≤ (1/2 : ℝ) := by
    calc
      _ ≤ q^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ht.le
      _ = 1/q := by rw [Real.rpow_neg_one,one_div]
      _ ≤ _ := one_div_le_one_div_of_le (by norm_num) hq
  exact (eventual_three_step_summable_bound (fun _ : Unit => f) 0 (f 0+f 1+f 2)
    (q^(3*t-(m:ℝ))) (add_nonneg (add_nonneg (hf 0) (hf 1)) (hf 2))
    (by positivity) hr (fun _ => hf)
    (fun _ e he => hb e (by simpa using he))
    (fun _ => ⟨(),fun e _ => (cubicKappaLocalMoment_add_three q C good m e t (by linarith)).le⟩) ()).1

end WaringSiegel
#print axioms WaringSiegel.cubicKappaLocalMoment_good_summable_bound
