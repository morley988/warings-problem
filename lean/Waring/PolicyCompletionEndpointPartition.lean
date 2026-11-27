import Waring.PolicyCompletionGoodBlocks
import Waring.SmoothBadEnergy
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact finite endpoint decomposition for the fundamental lemma

Every smooth endpoint either has zero derivative, has a marked coordinate
with no coprime block divisor, or belongs to the actual all-good family.
Deleting a marked coordinate is an exact, frequency-preserving bijection
onto the exceptional one-variable family already bounded in
`SmoothBadEnergy`. In particular no pointwise comparison of exponential
subsum norms is used.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionEndpointPartition
open AuxiliaryL2Grouping PolicyCompletionHolder PolicyCompletionGoodBlocks
open SmoothMoments SmoothBadFactorCount SmoothBadEnergy

def nonzeroAuxiliary {α : Type*} (A : Finset α) (D : α → ℕ) : Finset α := by
  classical
  exact A.filter (fun a => D a ≠ 0)

def zeroSmoothEndpoints {α : Type*} (s : ℕ) (A : Finset α)
    (Q R : ℝ) (D : α → ℕ) : Finset (α × (Fin s → ℕ)) := by
  classical
  exact (A.filter (fun a => D a = 0)) ×ˢ finiteTuples (smoothNumbers Q R) s

def markedBadEndpoints {α : Type*} (s : ℕ) (A : Finset α)
    (Q R M : ℝ) (D : α → ℕ) (i : Fin s) : Finset (α × (Fin s → ℕ)) := by
  classical
  exact (A ×ˢ finiteTuples (smoothNumbers Q R) s).filter (fun x =>
    D x.1 ≠ 0 ∧ x.2 i ∈ badSmoothNumbers Q R M (D x.1))

/-- The exceptional and all-good endpoint families cover every original
smooth tuple. The cover is allowed to overlap. -/
theorem endpoint_cover {α : Type*} (s : ℕ) (A : Finset α)
    (Q R M : ℝ) (D : α → ℕ) (x : α × (Fin s → ℕ))
    (hx : x ∈ A ×ˢ finiteTuples (smoothNumbers Q R) s) :
    x ∈ zeroSmoothEndpoints s A Q R D ∨
      (∃ i : Fin s, x ∈ markedBadEndpoints s A Q R M D i) ∨
      x ∈ goodSmoothEndpoints s A Q R M D := by
  classical
  by_cases hz : D x.1 = 0
  · exact Or.inl (Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hx).1,hz⟩,
        (Finset.mem_product.mp hx).2⟩)
  · by_cases hg : ∀ i : Fin s, ∃ d : ℕ,
        d ∈ CoefficientPower.coefficientBlock Q R M ∧ d ∣ x.2 i ∧ d.Coprime (D x.1)
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hx,hg⟩))
    · push_neg at hg
      obtain ⟨i,hi⟩ := hg
      refine Or.inr (Or.inl ⟨i,?_⟩)
      apply Finset.mem_filter.mpr
      refine ⟨hx,hz,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
      · exact Fintype.mem_piFinset.mp (Finset.mem_product.mp hx).2 i
      · rintro ⟨d,hd,hdn,hdc⟩
        exact hi d hd hdn hdc

/-- Removing one coordinate and keeping its value is an exact bijection. -/
def deleteCoordinateEquiv {α β : Type*} {s : ℕ} (i : Fin (s+1)) :
    (α × (Fin (s+1) → β)) ≃ ((α × (Fin s → β)) × β) where
  toFun x := ((x.1,i.removeNth x.2),x.2 i)
  invFun x := (x.1.1,i.insertNth x.2 x.1.2)
  left_inv x := Prod.ext rfl (Fin.insertNth_eq_iff.mpr ⟨rfl,rfl⟩)
  right_inv x := by simp

theorem deleteCoordinate_frequency {α β : Type*} {s : ℕ}
    (i : Fin (s+1)) (f : α → ℤ) (g : β → ℤ) (x : α × (Fin (s+1) → β)) :
    tupleFrequency f (fun _ => g) (deleteCoordinateEquiv i x).1 +
      g (deleteCoordinateEquiv i x).2 = tupleFrequency f (fun _ => g) x := by
  change (f x.1 + ∑ j : Fin s, g (x.2 (i.succAbove j))) + g (x.2 i) =
    f x.1 + ∑ j : Fin (s+1), g (x.2 j)
  rw [Fin.sum_univ_succAbove (fun j => g (x.2 j)) i]
  ring

/-- The coordinate-deletion bijection has exactly the exceptional domain
required by the proved bad-factor energy estimate. -/
theorem deleteCoordinate_mem_bad_iff {α : Type*} {s : ℕ}
    (i : Fin (s+1)) (A : Finset α) (Q R M : ℝ) (D : α → ℕ)
    (x : α × (Fin (s+1) → ℕ)) :
    deleteCoordinateEquiv i x ∈
      badEndpoints ((nonzeroAuxiliary A D) ×ˢ finiteTuples (smoothNumbers Q R) s)
        Q R M (fun a => D a.1) ↔
      x ∈ markedBadEndpoints (s+1) A Q R M D i := by
  classical
  simp only [badEndpoints,nonzeroAuxiliary,markedBadEndpoints,deleteCoordinateEquiv,
    Equiv.coe_fn_mk,Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨⟨ha,hd⟩,hu⟩,hi⟩,hb⟩
    refine ⟨⟨ha,Fintype.mem_piFinset.mpr ?_⟩,hd,hb⟩
    exact (Fin.forall_iff_succAbove i).mpr
      ⟨hi,Fintype.mem_piFinset.mp hu⟩
  · rintro ⟨⟨ha,hu⟩,hd,hb⟩
    have htu := Fintype.mem_piFinset.mp hu
    exact ⟨⟨⟨⟨ha,hd⟩,Fintype.mem_piFinset.mpr (fun j => htu (i.succAbove j))⟩,
      htu i⟩,hb⟩

/-- An exact finite frequency transport preserves collision cardinalities. -/
theorem collision_card_eq_of_equiv {α β : Type*} (e : α ≃ β)
    (A : Finset α) (B : Finset β) (f : α → ℤ) (g : β → ℤ)
    (hmem : ∀ x, e x ∈ B ↔ x ∈ A) (hfreq : ∀ x, g (e x)=f x) :
    (collisionPairs A f).card = (collisionPairs B g).card := by
  classical
  apply Finset.card_bij (fun p _ => (e p.1,e p.2))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(hmem p.1).mpr (Finset.mem_product.mp hp).1,
        (hmem p.2).mpr (Finset.mem_product.mp hp).2⟩,
      by simpa only [hfreq] using hf⟩
  · intro p hp q hq heq
    exact Prod.ext (e.injective (congrArg Prod.fst heq))
      (e.injective (congrArg Prod.snd heq))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hf⟩
    refine ⟨(e.symm p.1,e.symm p.2),Finset.mem_filter.mpr ⟨?_,?_⟩,by simp⟩
    · exact Finset.mem_product.mpr
        ⟨(hmem _).mp (by simpa using (Finset.mem_product.mp hp).1),
          (hmem _).mp (by simpa using (Finset.mem_product.mp hp).2)⟩
    · simpa only [← hfreq,e.apply_symm_apply] using hf

/-- The marked-coordinate energy is exactly the bad one-variable energy
with the remaining tuple incorporated into the auxiliary label. -/
theorem markedBad_collision_card_eq {α : Type*} {s : ℕ}
    (i : Fin (s+1)) (A : Finset α) (Q R M : ℝ) (D : α → ℕ)
    (f : α → ℤ) (g : ℕ → ℤ) :
    (collisionPairs (markedBadEndpoints (s+1) A Q R M D i)
      (tupleFrequency f (fun _ => g))).card =
    (collisionPairs
      (badEndpoints ((nonzeroAuxiliary A D) ×ˢ finiteTuples (smoothNumbers Q R) s)
        Q R M (fun a => D a.1))
      (fun x => tupleFrequency f (fun _ => g) x.1 + g x.2)).card := by
  exact collision_card_eq_of_equiv (deleteCoordinateEquiv i) _ _ _ _
    (deleteCoordinate_mem_bad_iff i A Q R M D)
    (deleteCoordinate_frequency i f g)

#print axioms endpoint_cover
#print axioms markedBad_collision_card_eq
end Waring.PolicyCompletionEndpointPartition
