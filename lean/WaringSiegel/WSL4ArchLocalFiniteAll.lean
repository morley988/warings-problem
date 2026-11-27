import WaringSiegel.WSL4ArchLocalFiniteField
import Mathlib.GroupTheory.OrderOfElement

/-! # The finite-field shortest-prefix bound for every positive exponent

Finiteness makes the monoid of positive power sums an additive subgroup:
an additive inverse is a finite repetition of the original sum.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 800000

theorem exists_power_list_nsmul {R : Type*} [CommRing R]
    (k : ℕ) (l : List R) (n : ℕ) :
    ∃m : List R,localPowerListSum k m=n • localPowerListSum k l := by
  induction n with
  | zero => exact ⟨[],by simp⟩
  | succ n ih =>
    obtain ⟨m,hm⟩ := ih
    exact ⟨m++l,by rw [localPowerListSum_append,hm,add_nsmul,one_nsmul]⟩

theorem exists_power_list_of_mem_finite_closure
    {R : Type*} [CommRing R] [Finite R] (k : ℕ) (a : R)
    (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^k))) :
    ∃l : List R,localPowerListSum k l=a := by
  let S : AddSubgroup R :=
    { carrier := {a | ∃l : List R,localPowerListSum k l=a}
      zero_mem' := ⟨[],rfl⟩
      add_mem' := by
        rintro a b ⟨l,rfl⟩ ⟨m,rfl⟩
        exact ⟨l++m,localPowerListSum_append k l m⟩
      neg_mem' := by
        rintro a ⟨l,hl⟩
        obtain ⟨m,hm⟩ := exists_power_list_nsmul k l (Nat.card R-1)
        refine ⟨m,hm.trans ?_⟩
        rw [hl]
        apply add_right_cancel (b:=a)
        calc
          (Nat.card R-1) • a+a=((Nat.card R-1)+1) • a := by
            rw [add_nsmul,one_nsmul]
          _=Nat.card R • a := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.card_pos (α:=R)))]
          _=0 := card_nsmul_eq_zero'
          _= -a+a := by simp }
  have hS : AddSubgroup.closure (Set.range (fun x : R => x^k))≤S :=
    (AddSubgroup.closure_le S).mpr (by
      rintro a ⟨x,rfl⟩
      exact ⟨[x],by simp⟩)
  exact hS ha

theorem finiteField_power_list
    {F : Type*} [Field F] [Finite F] (k : ℕ) (hk : 0<k) (a : F)
    (ha : a∈AddSubgroup.closure (Set.range (fun x : F => x^k))) :
    ∃l : List F,l.length≤k ∧ localPowerListSum k l=a := by
  obtain ⟨l,hl,hmin⟩ := exists_shortest_power_list k a
    (exists_power_list_of_mem_finite_closure k a ha)
  refine ⟨l,shortest_power_list_length_le k hk l ?_,hl⟩
  intro m hm
  exact hmin m (hm.trans hl)

#print axioms exists_power_list_of_mem_finite_closure
#print axioms finiteField_power_list
end WaringSiegel.WSL4
