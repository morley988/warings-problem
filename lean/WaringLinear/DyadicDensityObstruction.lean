import WaringLinear.DyadicObstruction
import Mathlib.Order.Interval.Finset.Nat

/-! # A fixed positive proportion of exceptions below the dyadic local width -/

namespace WaringLinear
open scoped BigOperators

/-- Representation with at most s positive roots. -/
def hasAtMostPositiveRoots (k s n : ℕ) : Prop :=
  ∃ t ≤ s, ∃ x : Fin t → ℕ, (∀ i, 0<x i) ∧ ∑ i, (x i)^k = n

noncomputable def exceptionalPositive (k s N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => ¬hasAtMostPositiveRoots k s n)

/-- At degree 2^(j+3), fewer than 4k summands miss at least
floor(N/(8k)) positive targets through N. -/
theorem dyadic_exceptional_card (j s N : ℕ) (hs : s<4*2^(j+3)) :
    N/(8*2^(j+3)) ≤ (exceptionalPositive (2^(j+3)) s N).card := by
  classical
  let k := 2^(j+3)
  let m := 8*k
  have hk : 0<k := by dsimp [k]; positivity
  have hm : 0<m := by dsimp [m]; positivity
  let f : ℕ → ℕ := fun a => m*a+4*k
  have hf : Function.Injective f := by
    intro a b h
    apply Nat.eq_of_mul_eq_mul_left hm
    exact Nat.add_right_cancel h
  have hsub : (Finset.range (N/m)).image f ⊆ exceptionalPositive k s N := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    have ha' : a+1≤N/m := Finset.mem_range.mp ha
    have hmul := (Nat.le_div_iff_mul_le hm).1 ha'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,?_⟩
    · dsimp [f]; omega
    · calc
        f a = m*a+4*k := rfl
        _ ≤ m*a+m := Nat.add_le_add_left (by dsimp [m]; omega) _
        _ = (a+1)*m := by ring
        _ ≤ N := hmul
    · rintro ⟨t,ht,x,_hx,he⟩
      exact dyadic_no_representation j a t x (lt_of_le_of_lt ht hs) he
  simpa only [Finset.card_image_of_injective _ hf,Finset.card_range] using
    Finset.card_le_card hsub

#print axioms dyadic_exceptional_card
end WaringLinear
