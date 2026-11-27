import WaringSiegel.WSL4RamanujamDigits

/-! # The uniform 4m coefficient budget at the sharp lifting precision -/
namespace WaringSiegel.WSL4Local

theorem powerDigitBudget_le_twice (p r : ℕ) (hp : 2≤p) :
    powerDigitBudget p (r+1)+1≤2*p^r := by
  induction r with
  | zero => simp [powerDigitBudget]
  | succ r ih =>
    rw [powerDigitBudget,pow_succ]
    have h := Nat.mul_le_mul_left p ih
    nlinarith

theorem powerDigitBudget_two (r : ℕ) : powerDigitBudget 2 r+1=2^r := by
  induction r with
  | zero => simp [powerDigitBudget]
  | succ r ih => rw [powerDigitBudget,pow_succ]; omega

theorem powerDigitBudget_sharp_precision (p r : ℕ) (hp : 2≤p) :
    powerDigitBudget p (r+if p=2 then 2 else 1)≤4*p^r := by
  by_cases hp2 : p=2
  · subst p
    simp only [ite_true]
    have h := powerDigitBudget_two (r+2)
    rw [pow_add] at h
    norm_num at h
    omega
  · simp only [if_neg hp2]
    have h := powerDigitBudget_le_twice p r hp
    omega

theorem coefficient_power_list_budget (p n r : ℕ) (hp : 2≤p) :
    n*powerDigitBudget p (r+if p=2 then 2 else 1)+1≤4*(n*p^r)+1 := by
  have h := Nat.mul_le_mul_left n (powerDigitBudget_sharp_precision p r hp)
  nlinarith

#print axioms coefficient_power_list_budget
end WaringSiegel.WSL4Local
