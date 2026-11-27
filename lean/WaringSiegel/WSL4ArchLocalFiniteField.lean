import WaringSiegel.WSL4ArchLocalPowerLists
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # Shortest power sums over actual finite fields

Nonzero partial sums of a shortest representation occupy distinct cosets of
the multiplicative subgroup of kth powers. Its index is at most k.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 900000
variable {F : Type*} [Field F] [Finite F]

theorem shortest_power_list_length_le (k : ℕ) (hk : 0<k) (l : List F)
    (hmin : ∀m : List F,localPowerListSum k m=localPowerListSum k l → l.length≤m.length) :
    l.length≤k := by
  let s : Fin l.length → F := fun i => localPowerListSum k (l.take (i.val+1))
  have hs (i : Fin l.length) : s i≠0 :=
    shortest_power_list_prefix_ne_zero k l hmin (i.val+1) (by omega) (by omega)
  let u : Fin l.length → Fˣ := fun i => Units.mk0 (s i) (hs i)
  let H : Subgroup Fˣ := (powMonoidHom k : Fˣ →* Fˣ).range
  let f : Fin l.length → Fˣ ⧸ H := fun i => (u i : Fˣ ⧸ H)
  have hneq {i j : Fin l.length} (hij : i.val<j.val) : f i≠f j := by
    intro he
    have he' : (u j : Fˣ ⧸ H)=(u i : Fˣ ⧸ H) := he.symm
    have hmem : u j/u i∈H := QuotientGroup.eq_iff_div_mem.mp he'
    obtain ⟨v,hv⟩ := hmem
    have hv' : (v:F)^k=s j/s i := by
      have hvv := congrArg (fun z : Fˣ => (z:F)) hv
      simpa only [powMonoidHom_apply,Units.val_pow_eq_pow_val,
        Units.val_div_eq_div_val,u,Units.val_mk0] using hvv
    have heq : s j=(v:F)^k*s i := by
      rw [hv',div_mul_cancel₀ _ (hs i)]
    exact shortest_power_list_no_scaled_prefix k l hmin (i.val+1) (j.val+1)
      (by omega) (by omega) (v:F) heq
  have hinj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij|hji
    · exact hneq hij he
    · exact hneq hji he.symm
  have hcard := Nat.card_le_card_of_injective f hinj
  have hindex : H.index=(Nat.card Fˣ).gcd k :=
    IsCyclic.index_powMonoidHom_range Fˣ k
  have hlen : l.length≤H.index := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin,Subgroup.index_eq_card] using hcard
  exact hlen.trans (hindex ▸ Nat.le_of_dvd hk (Nat.gcd_dvd_right _ _))

theorem finiteField_odd_power_list (k : ℕ) (hk : Odd k) (a : F)
    (ha : a∈AddSubgroup.closure (Set.range (fun x : F => x^k))) :
    ∃l : List F, l.length≤k ∧ localPowerListSum k l=a := by
  obtain ⟨l,hl,hmin⟩ := exists_shortest_power_list k a
    (exists_power_list_of_mem_odd_closure k hk a ha)
  refine ⟨l,shortest_power_list_length_le k hk.pos l ?_,hl⟩
  intro m hm
  exact hmin m (hm.trans hl)

#print axioms shortest_power_list_length_le
#print axioms finiteField_odd_power_list
end WaringSiegel.WSL4
