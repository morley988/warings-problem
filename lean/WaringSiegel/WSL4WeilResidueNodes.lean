import WaringSiegel.WSL4MajorRamanujamRelativeRing
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1200000

theorem exists_residue_distinct_nodes
    {B L : Type*} [CommRing B] [Field L] [Finite L]
    (rho : B →+* L) (hsurj : Function.Surjective rho)
    (P : ℕ) (hP : P<Nat.card L) :
    ∃ U : Fin (P+1) → B,Function.Injective (fun j => rho (U j)) := by
  letI : Fintype L := Fintype.ofFinite L
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α:=Fin (P+1)) (β:=L) (by
      rw [Fintype.card_fin,← Nat.card_eq_fintype_card]
      omega)
  choose U hU using fun j : Fin (P+1) => hsurj (e j)
  refine ⟨U,?_⟩
  intro i j hij
  apply e.injective
  simpa only [hU] using hij

theorem residue_distinct_node_denominator_coprime
    {B L : Type*} [CommRing B] [Field L]
    (p : ℕ) (rho : B →+* L) (hsurj : Function.Surjective rho)
    (hker : ∀b : B,rho b=0 ↔ (p:B)∣b)
    (P : ℕ) (U : Fin (P+1) → B)
    (hU : Function.Injective (fun j => rho (U j))) (j : Fin (P+1)) :
    IsCoprime (∏i∈Finset.univ.erase j,(U j-U i)) (p:B) := by
  apply IsCoprime.prod_left
  intro i hi
  apply WSL4.monogenic_coprime_of_residue_ne_zero p rho hsurj hker
  rw [map_sub]
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hi).1 (hU he).symm
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_residue_distinct_nodes
#print axioms WaringSiegel.WSL4Weil.residue_distinct_node_denominator_coprime
