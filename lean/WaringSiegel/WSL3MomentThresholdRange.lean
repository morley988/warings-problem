import WaringSiegel.Thresholds
import Mathlib.Tactic.Ring

/-! # The optimized integer threshold lies strictly above twice the degree -/
namespace WaringSiegel.Thresholds

theorem two_mul_le_two_pow (j : ℕ) (hj : 1≤j) : 2*j≤2^j := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  clear hj
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.succ_eq_add_one] at ih ⊢
    rw [pow_succ]
    nlinarith

theorem first_ge_twice_degree (k r : ℕ) (hk : 3≤k) (hrk : r≤k) :
    2*(k:ℚ)≤first k r := by
  have hkQ : (3:ℚ)≤k := by exact_mod_cast hk
  have hrQ : (r:ℚ)≤k := by exact_mod_cast hrk
  have hr0 : (0:ℚ)≤r := Nat.cast_nonneg _
  have hd : (0:ℚ)<k-r+1 := by linarith
  have hf : (r:ℚ)*(k-r-1)/(k-r+1)≤r :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  unfold first
  nlinarith

theorem second_ge_twice_degree (k j : ℕ) (hk : 3≤k) (hj : 1≤j) (hjk : j≤k) :
    2*(k:ℚ)≤second k j := by
  have hkQ : (3:ℚ)≤k := by exact_mod_cast hk
  have hjQ : (j:ℚ)≤k := by exact_mod_cast hjk
  have hp : 2*(j:ℚ)≤(2:ℚ)^j := by exact_mod_cast two_mul_le_two_pow j hj
  have hd : (0:ℚ)<k+1-j := by linarith
  have hn : (0:ℚ)≤((k:ℚ)-2)*(k+1)*(k-j) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hf : ((k:ℚ)*j-(2:ℚ)^j)/(k+1-j)≤(k:ℚ)^2-2*k :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  unfold second
  linarith

private theorem le_foldr_min_of_forall (a b : ℚ) (xs : List ℚ)
    (hb : a≤b) (hx : ∀ x∈xs,a≤x) : a≤xs.foldr min b := by
  induction xs with
  | nil => exact hb
  | cons x xs ih =>
    exact le_min (hx x (by simp)) (ih (fun y hy => hx y (by simp [hy])))

theorem threshold_ge_twice_degree (k : ℕ) (hk : 3≤k) : 2*(k:ℚ)≤threshold k := by
  unfold threshold
  apply le_foldr_min_of_forall
  · have hkQ : (3:ℚ)≤k := by exact_mod_cast hk
    nlinarith
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
      exact first_ge_twice_degree k (r+1) hk (by have := List.mem_range.mp hr; omega)
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      exact second_ge_twice_degree k (j+1) hk (by omega)
        (by have := List.mem_range.mp hj; omega)

theorem two_mul_lt_sufficientVariables (k : ℕ) (hk : 3≤k) :
    2*(k:ℤ)<sufficientVariables k := by
  have h := (threshold_ge_twice_degree k hk).trans_lt (strict_floor_threshold (threshold k))
  unfold sufficientVariables
  rw [if_neg (by omega)]
  exact_mod_cast h

theorem admissible_variables_gt_twice_degree (k s : ℕ) (hk : 3≤k)
    (hs : sufficientVariables k≤(s:ℤ)) : 2*k<s := by
  have h := (two_mul_lt_sufficientVariables k hk).trans_le hs
  exact_mod_cast h

#print axioms threshold_ge_twice_degree
#print axioms two_mul_lt_sufficientVariables
#print axioms admissible_variables_gt_twice_degree
end WaringSiegel.Thresholds
