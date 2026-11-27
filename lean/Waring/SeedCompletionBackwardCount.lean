import Waring.SeedCompletionBackward
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite Cauchy for the actual backward-differencing count

Frequency collisions make sense for any finite frequency family. Cauchy's
inequality bounds a cross count by the two complete self-collision counts.
Applied to the literal next-stage phase from `SeedCompletionBackward`, this
is the finite counting content of the source's Schwarz step. No moment
estimate or polynomial-count bound is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Waring.SeedCompletionBackwardCount
open Differences SeedCompletionBackward

/-- The actual ordered pairs whose two frequencies agree. -/
def crossFrequencyPairs {ι κ γ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → γ) (g : κ → γ) : Finset (ι × κ) := by
  classical
  exact (A ×ˢ B).filter (fun p => f p.1 = g p.2)

def frequencyFiber {ι γ : Type*} (A : Finset ι) (f : ι → γ) (n : γ) : Finset ι := by
  classical
  exact A.filter (fun x => f x=n)

/-- Exact decomposition into the products of the two fiber cardinalities. -/
theorem crossFrequencyPairs_card_eq_sum {ι κ γ : Type*}
    (A : Finset ι) (B : Finset κ) (f : ι → γ) (g : κ → γ)
    (N : Finset γ) (hN : ∀ x ∈ A, f x ∈ N) :
    (crossFrequencyPairs A B f g).card =
      ∑ n ∈ N, (frequencyFiber A f n).card * (frequencyFiber B g n).card := by
  classical
  unfold frequencyFiber
  have hmap : (crossFrequencyPairs A B f g).toSet.MapsTo (fun p => f p.1) N := by
    intro p hp
    exact hN p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro n hn
  have heq : (crossFrequencyPairs A B f g).filter (fun p => f p.1=n) =
      (A.filter (fun x => f x=n)) ×ˢ (B.filter (fun y => g y=n)) := by
    ext p
    simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hx,hy⟩,heq⟩,hn⟩
      exact ⟨⟨hx,hn⟩,hy,heq.symm.trans hn⟩
    · rintro ⟨⟨hx,hxn⟩,hy,hyn⟩
      exact ⟨⟨⟨hx,hy⟩,hxn.trans hyn.symm⟩,hxn⟩
  rw [heq,Finset.card_product]

/-- Finite Cauchy bounds the cross count by the actual self-collision
counts of the two unchanged frequency families. -/
theorem crossFrequencyPairs_card_sq_le {ι κ γ : Type*}
    (A : Finset ι) (B : Finset κ) (f : ι → γ) (g : κ → γ) :
    ((crossFrequencyPairs A B f g).card : ℝ)^2 ≤
      ((crossFrequencyPairs A A f f).card : ℝ) *
        ((crossFrequencyPairs B B g g).card : ℝ) := by
  classical
  let N := A.image f ∪ B.image g
  have hA : ∀ x ∈ A, f x ∈ N :=
    fun x hx => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
  have hB : ∀ y ∈ B, g y ∈ N :=
    fun y hy => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy)
  rw [crossFrequencyPairs_card_eq_sum A B f g N hA,
    crossFrequencyPairs_card_eq_sum A A f f N hA,
    crossFrequencyPairs_card_eq_sum B B g g N hB]
  unfold frequencyFiber
  push_cast
  simpa only [pow_two] using Finset.sum_mul_sq_le_sq_mul_sq N
    (fun n => ((A.filter (fun x => f x=n)).card : ℝ))
    (fun n => ((B.filter (fun y => g y=n)).card : ℝ))

/-- The source diagonal is bounded by the number of central integers times
the exact smooth-tuple collision count. -/
theorem diagonal_step_card_le {ι : Type*} (k : ℕ) (params : List (ℝ × ℝ))
    (w : ℤ) (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ) (hw : w ≠ 0) :
    (diagonalStepSolutions k params w Z B U).card ≤
      Z.card * (crossFrequencyPairs B B U U).card := by
  classical
  have hq : (w : ℝ)^k ≠ 0 := pow_ne_zero k (by exact_mod_cast hw)
  have hc : (diagonalStepSolutions k params w Z B U).card ≤
      (Z ×ˢ crossFrequencyPairs B B U U).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p.1.1,(p.1.2,p.2.2)))
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hdiag⟩
      rcases Finset.mem_filter.mp hp with ⟨hdom,_hdiv,heq⟩
      have hleft := Finset.mem_product.mp (Finset.mem_product.mp hdom).1
      have hright := Finset.mem_product.mp (Finset.mem_product.mp hdom).2
      apply Finset.mem_product.mpr
      refine ⟨hleft.1,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hleft.2,hright.2⟩,?_⟩⟩
      rw [hdiag] at heq
      exact mul_left_cancel₀ hq (add_left_cancel heq)
    · intro p hp r hr heq
      have hpd := (Finset.mem_filter.mp hp).2
      have hrd := (Finset.mem_filter.mp hr).2
      have hz : p.1.1=r.1.1 := congrArg (fun t : ℤ × (ι × ι) => t.1) heq
      have huv : (p.1.2,p.2.2)=(r.1.2,r.2.2) :=
        congrArg (fun t : ℤ × (ι × ι) => t.2) heq
      have hu : p.1.2=r.1.2 := congrArg (fun t : ι × ι => t.1) huv
      have hv : p.2.2=r.2.2 := congrArg (fun t : ι × ι => t.2) huv
      exact Prod.ext (Prod.ext hz hu) (Prod.ext (hpd.symm.trans (hz.trans hrd)) hv)
  simpa only [Finset.card_product] using hc

/-- The literal center/height domain for the next auxiliary polynomial. -/
def nextParameterDomain (w P : ℤ) (k : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc 2 (2*P) ×ˢ Finset.Icc 1 (P/w^k)

def nextPhase (k : ℕ) (params : List (ℝ × ℝ)) (w : ℤ) (p : ℤ × ℤ) : ℝ :=
  modifiedCenteredPower k (((p.2 : ℝ),(w : ℝ)) :: scaleHeights 2 params) p.1

/-- Reassociating the actual variables identifies the next-stage count
with one finite cross-frequency count, preserving all endpoints. -/
theorem nextStepSolutions_card_eq_cross {ι : Type*} (k : ℕ)
    (params : List (ℝ × ℝ)) (w P : ℤ) (B : Finset ι) (U : ι → ℝ) :
    (nextStepSolutions k params w P B U).card =
      (crossFrequencyPairs (nextParameterDomain w P k ×ˢ B) B
        (fun p => nextPhase k params w p.1 + (2 : ℝ)^k*U p.2)
        (fun u => (2 : ℝ)^k*U u)).card := by
  classical
  apply Finset.card_equiv (Equiv.prodAssoc (ℤ × ℤ) ι ι).symm
  intro p
  simp only [nextStepSolutions,crossFrequencyPairs,nextParameterDomain,nextPhase,
    Finset.mem_filter,Finset.mem_product,Equiv.prodAssoc_symm_apply]
  tauto

/-- The actual next-stage count satisfies the source Schwarz inequality
in squared form. Both factors are complete, unchanged collision counts. -/
theorem next_step_card_sq_le {ι : Type*} (k : ℕ)
    (params : List (ℝ × ℝ)) (w P : ℤ) (B : Finset ι) (U : ι → ℝ) :
    ((nextStepSolutions k params w P B U).card : ℝ)^2 ≤
      ((crossFrequencyPairs (nextParameterDomain w P k ×ˢ B)
        (nextParameterDomain w P k ×ˢ B)
        (fun p => nextPhase k params w p.1 + (2 : ℝ)^k*U p.2)
        (fun p => nextPhase k params w p.1 + (2 : ℝ)^k*U p.2)).card : ℝ) *
      ((crossFrequencyPairs B B (fun u => (2 : ℝ)^k*U u)
        (fun u => (2 : ℝ)^k*U u)).card : ℝ) := by
  rw [nextStepSolutions_card_eq_cross]
  exact crossFrequencyPairs_card_sq_le _ _ _ _

/-- The literal backward step with its diagonal count fully evaluated.
The next-stage factor is bounded independently by `next_step_card_sq_le`. -/
theorem step_card_le_tuple_diagonal_add_next {ι : Type*} (k : ℕ)
    (params : List (ℝ × ℝ)) (w P : ℤ) (Z : Finset ℤ) (B : Finset ι) (U : ι → ℝ)
    (hw : 0 < w) (hZ : Z ⊆ Finset.Icc 1 P) :
    (stepSolutions k params w Z B U).card ≤
      Z.card*(crossFrequencyPairs B B U U).card +
        2*(nextStepSolutions k params w P B U).card :=
  (step_card_le_diagonal_add_next k params w P Z B U hw hZ).trans
    (Nat.add_le_add_right (diagonal_step_card_le k params w Z B U hw.ne') _)

#print axioms crossFrequencyPairs_card_sq_le
#print axioms diagonal_step_card_le
#print axioms next_step_card_sq_le
#print axioms step_card_le_tuple_diagonal_add_next

end Waring.SeedCompletionBackwardCount
