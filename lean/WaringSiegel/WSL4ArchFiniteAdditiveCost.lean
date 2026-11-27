import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-! # The integer cost of cyclic steps in a finite p-group -/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000

theorem cyclic_prime_power_cost (p b t : ℕ) (hp : 2≤p) (hb : 1≤b) (hbt : b≤t) :
    t*(p^b-1)≤b*(p^t-1) := by
  induction t,hbt using Nat.le_induction with
  | base => rfl
  | succ t hbt ih =>
    have hp1 : 1≤p := by omega
    have hpow : p^b≤p^t := Nat.pow_le_pow_right hp1 hbt
    have hpow1 : 1≤p^t := one_le_pow₀ hp1
    have hpb1 : 1≤p^b := one_le_pow₀ hp1
    have hprod : 1≤b*(p-1) := Nat.mul_pos hb (by omega)
    have haux : p^b-1≤b*(p-1)*p^t :=
      (Nat.sub_le _ _).trans (hpow.trans (by nlinarith))
    have hsub : p^(t+1)-1=(p^t-1)+(p-1)*p^t := by
      rw [pow_succ]
      nlinarith [Nat.sub_add_cancel hp1,Nat.sub_add_cancel hpow1,
        Nat.sub_add_cancel (Nat.mul_le_mul hpow1 hp1)]
    rw [hsub,Nat.add_mul,Nat.one_mul,Nat.mul_add]
    nlinarith

theorem list_lift_of_mem_image
    {G H : Type*} (f : G → H) (S : Set G) (l : List H)
    (hl : ∀y∈l,y∈f '' S) :
    ∃m : List G,(∀x∈m,x∈S) ∧ m.length=l.length ∧ m.map f=l := by
  induction l with
  | nil => exact ⟨[],by simp,by simp,by simp⟩
  | cons y l ih =>
    obtain ⟨x,hx,rfl⟩ := hl y (by simp)
    obtain ⟨m,hm,hlen,hmap⟩ := ih (fun z hz => hl z (by simp [hz]))
    refine ⟨x::m,?_,by simp [hlen],by simp [hmap]⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact hx
    · exact hm z hz

#print axioms cyclic_prime_power_cost
#print axioms list_lift_of_mem_image
end WaringSiegel.WSL4
