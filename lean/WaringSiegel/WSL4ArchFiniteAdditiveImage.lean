import WaringSiegel.WSL4ArchFiniteAdditiveCount
import Mathlib.GroupTheory.PGroup

/-! # Quantitative positive lists from arbitrary generating images

The source type need not be finite. The finite target group may be bounded
above by p^Q, and only membership in the generated subgroup is required.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1400000

theorem finite_additive_generator_count_card_le
    (p t Q : ℕ) (hp : Nat.Prime p) (ht : 0<t)
    {G : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G≤p^Q) (hexp : ∀x : G,(p^t) • x=0)
    (S : Set G) (hS : AddSubgroup.closure S=⊤) (a : G) :
    ∃l : List G,(∀x∈l,x∈S) ∧ l.sum=a ∧ l.length*t≤Q*(p^t-1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p (Multiplicative G) := by
    intro x
    refine ⟨t,?_⟩
    change (p^t) • (Multiplicative.toAdd x)=0
    exact hexp _
  obtain ⟨q,hq⟩ := IsPGroup.exists_card_eq hpg
  change Nat.card G=p^q at hq
  have hqQ : q≤Q := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hq ▸ hcard)
  obtain ⟨l,hl,hsum,hbound⟩ := finite_additive_generator_count p t q hp ht hq hexp S hS a
  exact ⟨l,hl,hsum,hbound.trans (Nat.mul_le_mul_right _ hqQ)⟩

theorem finite_additive_closure_list_count
    (p t Q : ℕ) (hp : Nat.Prime p) (ht : 0<t)
    {G : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G≤p^Q) (hexp : ∀x : G,(p^t) • x=0)
    (S : Set G) (a : G) (ha : a∈AddSubgroup.closure S) :
    ∃l : List G,(∀x∈l,x∈S) ∧ l.sum=a ∧ l.length*t≤Q*(p^t-1) := by
  let H : AddSubgroup G := AddSubgroup.closure S
  let T : Set H := {x | (x:G)∈S}
  have hT : AddSubgroup.closure T=⊤ := by
    apply top_unique
    intro x hx
    have hmap : H≤(AddSubgroup.closure T).map H.subtype := by
      apply (AddSubgroup.closure_le _).mpr
      intro y hy
      exact ⟨⟨y,AddSubgroup.subset_closure hy⟩,AddSubgroup.subset_closure hy,rfl⟩
    obtain ⟨y,hy,he⟩ := hmap x.property
    have hxy : y=x := Subtype.ext he
    exact hxy ▸ hy
  have hcardH : Nat.card H≤p^Q :=
    (Nat.card_le_card_of_injective (fun x : H => (x:G)) Subtype.val_injective).trans hcard
  have hexpH : ∀x : H,(p^t) • x=0 := by
    intro x
    apply Subtype.ext
    exact hexp (x:G)
  obtain ⟨l,hl,hsum,hbound⟩ := finite_additive_generator_count_card_le p t Q hp ht
    hcardH hexpH T hT (⟨a,ha⟩:H)
  refine ⟨l.map H.subtype,?_,?_,by simpa only [List.length_map] using hbound⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    exact hl y hy
  · rw [← map_list_sum,hsum]
    rfl

theorem finite_additive_image_list_count
    (p t Q : ℕ) (hp : Nat.Prime p) (ht : 0<t)
    {G A : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G≤p^Q) (hexp : ∀x : G,(p^t) • x=0)
    (f : A → G) (a : G) (ha : a∈AddSubgroup.closure (Set.range f)) :
    ∃l : List A,(l.map f).sum=a ∧ l.length*t≤Q*(p^t-1) := by
  obtain ⟨m,hm,hsum,hbound⟩ := finite_additive_closure_list_count p t Q hp ht hcard hexp
    (Set.range f) a ha
  have himage : ∀y∈m,y∈f '' (Set.univ : Set A) := by
    intro y hy
    obtain ⟨x,rfl⟩ := hm y hy
    exact ⟨x,Set.mem_univ _,rfl⟩
  obtain ⟨l,-,hlen,hmap⟩ := list_lift_of_mem_image f Set.univ m himage
  exact ⟨l,by rw [hmap,hsum],by simpa only [hlen] using hbound⟩

theorem finite_additive_image_list_count_scaled
    (p t Q M : ℕ) (hp : Nat.Prime p) (ht : 0<t) (hQ : Q≤t*M)
    {G A : Type*} [AddCommGroup G] [Finite G]
    (hcard : Nat.card G≤p^Q) (hexp : ∀x : G,(p^t) • x=0)
    (f : A → G) (a : G) (ha : a∈AddSubgroup.closure (Set.range f)) :
    ∃l : List A,(l.map f).sum=a ∧ l.length≤M*(p^t-1) := by
  obtain ⟨l,hl,hbound⟩ := finite_additive_image_list_count p t Q hp ht hcard hexp f a ha
  refine ⟨l,hl,?_⟩
  have hh : l.length*t≤(M*(p^t-1))*t :=
    (hbound.trans (Nat.mul_le_mul_right _ hQ)).trans_eq (by ring)
  exact le_of_mul_le_mul_right hh ht

#print axioms finite_additive_generator_count_card_le
#print axioms finite_additive_closure_list_count
#print axioms finite_additive_image_list_count
#print axioms finite_additive_image_list_count_scaled
end WaringSiegel.WSL4
