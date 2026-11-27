import WaringSiegel.WSL4ArchFiniteAdditiveCost
import Mathlib.Data.ZMod.QuotientGroup

/-! # Positive-generator length in a finite additive p-group

An exponent bound p^t and order p^Q give the exact weighted length bound
length*t <= Q*(p^t-1). Every summand belongs to the supplied generating set.
The proof successively quotients by one actual nonzero generator.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1600000

theorem finite_additive_generator_count
    (p t Q : ℕ) (hp : Nat.Prime p) (ht : 0<t)
    {G : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G=p^Q) (hexp : ∀x : G,(p^t) • x=0)
    (S : Set G) (hS : AddSubgroup.closure S=⊤) (a : G) :
    ∃l : List G,(∀x∈l,x∈S) ∧ l.sum=a ∧ l.length*t≤Q*(p^t-1) := by
  induction Q using Nat.strong_induction_on generalizing G with
  | h Q ih =>
    by_cases hnon : ∃x∈S,x≠0
    · obtain ⟨x,hxS,hx0⟩ := hnon
      let H : AddSubgroup G := AddSubgroup.zmultiples x
      let q : G →+ G ⧸ H := QuotientAddGroup.mk' H
      have hq : Function.Surjective q := QuotientAddGroup.mk'_surjective H
      have hord : addOrderOf x∣p^Q := hcard ▸ addOrderOf_dvd_natCard x
      obtain ⟨b,hbQ,hb⟩ := (Nat.dvd_prime_pow hp).mp hord
      have hb0 : 0<b := by
        by_contra hh
        have hbz : b=0 := by omega
        have horder1 : addOrderOf x=1 := by simpa [hbz] using hb
        have hxsmul := addOrderOf_nsmul_eq_zero x
        rw [horder1,one_nsmul] at hxsmul
        exact hx0 hxsmul
      have hbt : b≤t := by
        have hd : addOrderOf x∣p^t := addOrderOf_dvd_of_nsmul_eq_zero (hexp x)
        have hl := Nat.le_of_dvd (pow_pos hp.pos t) hd
        rw [hb] at hl
        exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hl
      have hprod : p^b*Nat.card (G ⧸ H)=p^Q := by
        have hh := H.card_mul_index
        rw [AddSubgroup.index_eq_card] at hh
        change Nat.card (AddSubgroup.zmultiples x)*Nat.card (G ⧸ H)=Nat.card G at hh
        simpa only [Nat.card_zmultiples,hb,hcard] using hh
      have hcardq : Nat.card (G ⧸ H)=p^(Q-b) := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos b)
        calc
          p^b*Nat.card (G ⧸ H)=p^Q := hprod
          _=p^b*p^(Q-b) := by rw [← pow_add,Nat.add_sub_cancel' hbQ]
      have hQb : Q-b<Q := Nat.sub_lt (by omega) hb0
      have hexpq : ∀y : G ⧸ H,(p^t) • y=0 := by
        intro y
        obtain ⟨z,rfl⟩ := hq y
        rw [← map_nsmul,hexp,map_zero]
      have hSq : AddSubgroup.closure (q '' S)=⊤ := by
        rw [← AddMonoidHom.map_closure,hS,AddSubgroup.map_top_of_surjective q hq]
      obtain ⟨l,hlS,hla,hlbound⟩ := ih (Q-b) hQb hcardq hexpq (q '' S) hSq (q a)
      obtain ⟨m,hmS,hmLen,hmMap⟩ := list_lift_of_mem_image q S l hlS
      have hma : q m.sum=q a := by
        rw [map_list_sum,hmMap,hla]
      have hdiff : a-m.sum∈H := by
        apply (QuotientAddGroup.eq_zero_iff _).mp
        change q (a-m.sum)=0
        rw [map_sub,hma,sub_self]
      have hmem := mem_zmultiples_iff_mem_range_addOrderOf.mp hdiff
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hmem
      have hjlt : j<p^b := by simpa only [Finset.mem_range,hb] using hj
      refine ⟨List.replicate j x++m,?_,?_,?_⟩
      · intro z hz
        rcases List.mem_append.mp hz with hz|hz
        · rcases List.mem_replicate.mp hz with ⟨_,rfl⟩
          exact hxS
        · exact hmS z hz
      · rw [List.sum_append,List.sum_replicate,he]
        abel
      · simp only [List.length_append,List.length_replicate,hmLen,Nat.add_mul]
        have hjcost : j*t≤b*(p^t-1) := by
          calc
            j*t≤(p^b-1)*t := Nat.mul_le_mul_right t (by omega)
            _≤b*(p^t-1) := by simpa only [Nat.mul_comm] using
              cyclic_prime_power_cost p b t hp.two_le (by omega) hbt
        calc
          j*t+l.length*t≤b*(p^t-1)+(Q-b)*(p^t-1) := Nat.add_le_add hjcost hlbound
          _=Q*(p^t-1) := by rw [← Nat.add_mul,Nat.add_sub_cancel' hbQ]
    · have hle : AddSubgroup.closure S≤⊥ := by
        apply (AddSubgroup.closure_le _).mpr
        intro x hx
        change x=0
        by_contra hx0
        exact hnon ⟨x,hx,hx0⟩
      have ha : a=0 := hle (hS ▸ AddSubgroup.mem_top a)
      exact ⟨[],by simp,by simp [ha],by simp⟩

#print axioms finite_additive_generator_count
end WaringSiegel.WSL4
