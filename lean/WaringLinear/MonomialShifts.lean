import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Ring

/-! # The leading coefficient after independent Weyl shifts -/

namespace WaringLinear
open scoped BigOperators
open Finset

def mixedShifts : List ℕ → (ℤ → ℤ) → ℤ → ℤ
  | [],f => f
  | h::t,f => fwdDiff (h:ℤ) (mixedShifts t f)

private theorem commute_one_shift (u : ℤ) (f : ℤ → ℤ) :
    fwdDiff u (fwdDiff 1 f) = fwdDiff 1 (fwdDiff u f) := by
  funext x
  simp only [fwdDiff]
  rw [show x+u+1=x+1+u by ring]
  ring

private theorem commute_unit_shifts (t : List ℕ) (f : ℤ → ℤ) :
    mixedShifts t (fwdDiff 1 f) = fwdDiff 1 (mixedShifts t f) := by
  induction t with
  | nil => rfl
  | cons h t ih => simp only [mixedShifts,ih,commute_one_shift]

private theorem shift_telescope (f : ℤ → ℤ) (h : ℕ) (x : ℤ) :
    fwdDiff (h:ℤ) f x = ∑ j∈range h,fwdDiff 1 f (x+j) := by
  induction h with
  | zero => simp [fwdDiff]
  | succ h ih =>
    rw [sum_range_succ,←ih]
    simp only [fwdDiff,Nat.cast_succ,←add_assoc]
    ring

theorem mixed_shifts_of_unit_iterate (t : List ℕ) (f : ℤ → ℤ) (c : ℤ)
    (hf : ∀ x, (fwdDiff (1:ℤ))^[t.length] f x=c) :
    ∀ x, mixedShifts t f x = (t.prod:ℤ)*c := by
  induction t generalizing f with
  | nil => simpa [mixedShifts] using hf
  | cons h t ih =>
    have hnext : ∀ x,(fwdDiff (1:ℤ))^[t.length] (fwdDiff 1 f) x=c := by
      simpa only [List.length_cons,Function.iterate_succ_apply] using hf
    have hbase := ih (fwdDiff 1 f) hnext
    rw [commute_unit_shifts] at hbase
    intro x
    simp only [mixedShifts,shift_telescope,hbase,sum_const,card_range,nsmul_eq_mul,
      List.prod_cons,Nat.cast_mul]
    ring

/-- The final constant after k arbitrary nonnegative shifts is k! times
their product. Negative shifts amount to a translated positive shift
and an additional sign. -/
theorem mixed_monomial_coefficient (t : List ℕ) (x : ℤ) :
    mixedShifts t (fun u : ℤ => u^t.length) x = (t.prod:ℤ)*t.length.factorial := by
  apply mixed_shifts_of_unit_iterate
  intro y
  rw [fwdDiff_iter_eq_factorial]
  rfl

#print axioms mixed_monomial_coefficient
end WaringLinear
