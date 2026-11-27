import Waring.SeedCompletionNaturalScales
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Full source boxes are invariant under paired coordinate permutations -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges CartesianProductSampling PolicyCompletionHolder
open SmoothMoments

def reindexNatural {j : ℕ} (σ : Equiv.Perm (Fin j)) (p : NaturalLabel j × ℕ) :
    NaturalLabel j × ℕ := ((p.1.1 ∘ σ,p.1.2 ∘ σ),p.2)

theorem reindexNatural_injective {j : ℕ} (σ : Equiv.Perm (Fin j)) :
    Function.Injective (reindexNatural σ) := by
  intro p q hpq
  apply Prod.ext
  · apply Prod.ext
    · funext i
      have H := congrArg (fun x : NaturalLabel j × ℕ => x.1.1 (σ.symm i)) hpq
      simpa only [reindexNatural,Function.comp_apply,Equiv.apply_symm_apply] using H
    · funext i
      have H := congrArg (fun x : NaturalLabel j × ℕ => x.1.2 (σ.symm i)) hpq
      simpa only [reindexNatural,Function.comp_apply,Equiv.apply_symm_apply] using H
  · simpa only [reindexNatural] using congrArg (fun x : NaturalLabel j × ℕ => x.2) hpq

theorem reindexNatural_mem {j : ℕ} (k : ℕ) (L P R : ℝ) (M : Fin j → ℝ)
    (σ : Equiv.Perm (Fin j)) {p : NaturalLabel j × ℕ}
    (hp : p∈naturalBoxDomain k L P R M) :
    reindexNatural σ p∈naturalBoxDomain k L P R (M ∘ σ) := by
  obtain ⟨hp,hz⟩ := Finset.mem_product.mp hp
  obtain ⟨hh,hm⟩ := Finset.mem_product.mp hp
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hz⟩
  · apply mem_positiveBox.mpr
    intro i
    exact mem_positiveBox.mp hh (σ i)
  · apply Fintype.mem_piFinset.mpr
    intro i
    exact Fintype.mem_piFinset.mp hm (σ i)

theorem naturalBoxDomain_reindex {j : ℕ} (k : ℕ) (L P R : ℝ) (M : Fin j → ℝ)
    (σ : Equiv.Perm (Fin j)) :
    (naturalBoxDomain k L P R M).image (reindexNatural σ)=
      naturalBoxDomain k L P R (M ∘ σ) := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact reindexNatural_mem k L P R M σ hq
  · intro p hp
    have H := reindexNatural_mem k L P R (M ∘ σ) σ.symm hp
    have heq : (M ∘ σ) ∘ σ.symm=M := by funext i; simp
    rw [heq] at H
    refine Finset.mem_image.mpr ⟨reindexNatural σ.symm p,H,?_⟩
    ext i <;> simp [reindexNatural]

theorem naturalPhase_reindex {j : ℕ} (k : ℕ) (L P R : ℝ) (M : Fin j → ℝ)
    (σ : Equiv.Perm (Fin j)) {p : NaturalLabel j × ℕ}
    (hp : p∈naturalBoxDomain k L P R M) :
    naturalPhase k (reindexNatural σ p)=naturalPhase k p := by
  have hm := (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2
  have hparams : ∀ a∈naturalParameters (p.1.1 ∘ σ) (p.1.2 ∘ σ),a.2≠0 := by
    simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro i
    exact_mod_cast (boxCoefficientTuples_pos P R M hm (σ i)).ne'
  have H := powerPolynomial_perm k
    (σ.ofFn_comp_perm (fun i => ((p.1.1 i:ℤ),(p.1.2 i:ℤ)))) hparams
  exact congrArg (fun f : Polynomial ℤ => f.eval (p.2:ℤ)) H

theorem boxSourceFamily_reindex {j : ℕ} (k : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (σ : Equiv.Perm (Fin j)) (α : ℝ) :
    boxSourceFamily k L P R (M ∘ σ) α=boxSourceFamily k L P R M α := by
  classical
  rw [boxSourceFamily_eq_frequency,boxSourceFamily_eq_frequency,← naturalBoxDomain_reindex]
  unfold frequencySum
  rw [Finset.sum_image (fun _ _ _ _ heq => reindexNatural_injective σ heq)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [naturalPhase_reindex k L P R M σ hp]

theorem total_reindex {j : ℕ} (φ : Fin j → ℝ) (σ : Equiv.Perm (Fin j)) :
    total (φ ∘ σ)=total φ := by
  exact Equiv.sum_comp σ φ

theorem powerBoxCross_reindex {j : ℕ} (k s : ℕ) (D : ℝ) (φ : Fin j → ℝ)
    (σ : Equiv.Perm (Fin j)) (P R : ℝ) :
    powerBoxCross k s D (φ ∘ σ) P R=powerBoxCross k s D φ P R := by
  unfold powerBoxCross boxCrossMoment
  rw [total_reindex]
  apply intervalIntegral.integral_congr
  intro α hα
  dsimp only
  rw [show (fun i => P^((φ ∘ σ) i))=(fun i => P^(φ i)) ∘ σ by rfl,
    boxSourceFamily_reindex]

theorem powerBoxMixed_reindex {j : ℕ} (k s : ℕ) (D : ℝ) (φ : Fin j → ℝ)
    (σ : Equiv.Perm (Fin j)) (P R : ℝ) :
    powerBoxMixed k s D (φ ∘ σ) P R=powerBoxMixed k s D φ P R := by
  unfold powerBoxMixed boxMixedMoment
  rw [total_reindex]
  apply intervalIntegral.integral_congr
  intro α hα
  dsimp only
  rw [show (fun i => P^((φ ∘ σ) i))=(fun i => P^(φ i)) ∘ σ by rfl,
    boxSourceFamily_reindex]

theorem powerBoxCross_snoc {j : ℕ} (k s : ℕ) (D ψ : ℝ) (φ : Fin j → ℝ) (P R : ℝ) :
    powerBoxCross k s D (Fin.snoc φ ψ) P R=powerBoxCross k s D (Fin.cons ψ φ) P R := by
  rw [Fin.snoc_eq_cons_rotate]
  exact powerBoxCross_reindex k s D (Fin.cons ψ φ) (finRotate (j+1)) P R

theorem powerBoxMixed_snoc {j : ℕ} (k s : ℕ) (D ψ : ℝ) (φ : Fin j → ℝ) (P R : ℝ) :
    powerBoxMixed k s D (Fin.snoc φ ψ) P R=powerBoxMixed k s D (Fin.cons ψ φ) P R := by
  rw [Fin.snoc_eq_cons_rotate]
  exact powerBoxMixed_reindex k s D (Fin.cons ψ φ) (finRotate (j+1)) P R

#print axioms powerBoxCross_snoc
#print axioms powerBoxMixed_snoc
end Waring.SeedCompletionNaturalBox
