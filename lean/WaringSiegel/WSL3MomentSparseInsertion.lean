import WaringSiegel.WSL3MomentInsertion
import WaringSiegel.WSL3MomentSparseCritical

/-!
# Inserting the lower equations in a sparse power system

The top-degree moment is bounded by the full sparse energy times the exact
number of possible lower power-sum differences. This is a finite theorem,
valid for every coefficient ring with injective integer coordinates.
-/

set_option maxHeartbeats 400000

noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL3
open WSL2

variable {ι α A : Type*} [Fintype ι] [Fintype α] [CommRing A]

def powerDifferenceImage (nodes : α → A) (j s : ℕ) : Finset A :=
  Finset.univ.image (fun xy : (Fin s → α) × (Fin s → α) =>
    (∑ i, nodes (xy.1 i)^j) - ∑ i, nodes (xy.2 i)^j)

theorem sparseDegree_castSucc (k R : ℕ) (j : Fin R) :
    sparseDegree k (R+1) j.castSucc = j.val+1 := by
  simp only [sparseDegree, Fin.coe_castSucc, if_neg (by omega : j.val+1 ≠ R+1)]

theorem sparseDegree_last (k R : ℕ) : sparseDegree k (R+1) (Fin.last R) = k := by
  simp [sparseDegree]

theorem sparse_insertion_bound (coord : A →+ (ι → ℤ)) (hcoord : Function.Injective coord)
    (nodes : α → A) (k R s : ℕ) :
    (frequencyEnergy (fun x : Fin s → α => coord (∑ i, nodes (x i)^k)) : ℝ) ≤
      (∏ j : Fin R, ((powerDifferenceImage nodes (j.val+1) s).card : ℝ)) *
        weightedSystemEnergy s (fun x => sparseValue k (R+1) (nodes x)) (fun _ => 1) := by
  let V : (Fin s → α) → Fin (R+1) × ι → ℤ := fun x =>
    systemCoordinates coord (R+1) (∑ i, sparseValue k (R+1) (nodes (x i)))
  let T := Finset.univ.filter (fun xy : (Fin s → α) × (Fin s → α) =>
    coord (∑ i, nodes (xy.1 i)^k) = coord (∑ i, nodes (xy.2 i)^k))
  let box := Fintype.piFinset (fun j : Fin R => powerDifferenceImage nodes (j.val+1) s)
  let D := box.image (fun a : Fin R → A => systemCoordinates coord (R+1) (Fin.snoc a 0))
  have hcover : ∀ xy ∈ T, V xy.1 - V xy.2 ∈ D := by
    intro xy hxy
    have htop : (∑ i, nodes (xy.1 i)^k) = ∑ i, nodes (xy.2 i)^k :=
      hcoord (Finset.mem_filter.mp hxy).2
    let a : Fin R → A := fun j =>
      (∑ i, nodes (xy.1 i)^(j.val+1)) - ∑ i, nodes (xy.2 i)^(j.val+1)
    have ha : a ∈ box := by
      apply Fintype.mem_piFinset.mpr
      intro j
      exact Finset.mem_image.mpr ⟨xy, Finset.mem_univ _, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨a, ha, ?_⟩
    dsimp [V]
    rw [← map_sub]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last, Pi.sub_apply, Finset.sum_apply, sparseValue,
        sparseDegree_last, htop, sub_self]
    · simp only [Fin.snoc_castSucc, Pi.sub_apply, Finset.sum_apply, sparseValue,
        sparseDegree_castSucc, a]
  have hbound := frequencyEnergy_projection_bound V T D hcover
  have hcard : D.card ≤ ∏ j : Fin R, (powerDifferenceImage nodes (j.val+1) s).card := by
    exact (Finset.card_image_le).trans_eq (Fintype.card_piFinset _)
  have hn : T.card ≤ (∏ j : Fin R, (powerDifferenceImage nodes (j.val+1) s).card) *
      frequencyEnergy V := hbound.trans (Nat.mul_le_mul_right _ hcard)
  have hre : (T.card : ℝ) ≤ (∏ j : Fin R,
      ((powerDifferenceImage nodes (j.val+1) s).card : ℝ)) * (frequencyEnergy V : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using (show (T.card : ℝ) ≤
      ((∏ j : Fin R, (powerDifferenceImage nodes (j.val+1) s).card) * frequencyEnergy V : ℕ) from
        Nat.cast_le.mpr hn)
  have he : (frequencyEnergy V : ℝ) = weightedSystemEnergy s
      (fun x => sparseValue k (R+1) (nodes x)) (fun _ => 1) :=
    frequencyEnergy_systemCoordinates coord hcoord (R+1) s
      (fun x => sparseValue k (R+1) (nodes x))
  exact hre.trans_eq (congrArg (fun z : ℝ =>
    (∏ j : Fin R, ((powerDifferenceImage nodes (j.val+1) s).card : ℝ))*z) he)


#print axioms sparse_insertion_bound

end WaringSiegel.WSL3
