import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring

/-!
# Product-norm separation for close pairs

This file proves the archimedean determinant estimate used by product-shaped
arcs.  The arithmetic lower bound for nonzero elements of an ideal is an
explicit premise, so the result is not a surrogate for that arithmetic input.
-/

noncomputable section

open scoped BigOperators

namespace WaringSiegel

theorem close_pair_determinant_norm_bound
    (θ u₁ u₂ b₁ b₂ : ℂ) (P Z : ℝ) (hZ : 0 ≤ Z)
    (hu₁ : ‖u₁‖ ≤ P) (hu₂ : ‖u₂‖ ≤ P)
    (hb₁ : ‖b₁ - θ * u₁‖ ≤ Z) (hb₂ : ‖b₂ - θ * u₂‖ ≤ Z) :
    ‖b₁ * u₂ - b₂ * u₁‖ ≤ 2 * P * Z := by
  have hid : b₁ * u₂ - b₂ * u₁ =
      (b₁ - θ * u₁) * u₂ - (b₂ - θ * u₂) * u₁ := by ring
  rw [hid]
  calc
    ‖(b₁ - θ * u₁) * u₂ - (b₂ - θ * u₂) * u₁‖ ≤
        ‖b₁ - θ * u₁‖ * ‖u₂‖ + ‖b₂ - θ * u₂‖ * ‖u₁‖ := by
      simpa only [norm_mul] using
        norm_sub_le ((b₁ - θ * u₁) * u₂) ((b₂ - θ * u₂) * u₁)
    _ ≤ Z * P + Z * P := add_le_add
      (mul_le_mul hb₁ hu₂ (norm_nonneg _) hZ)
      (mul_le_mul hb₂ hu₁ (norm_nonneg _) hZ)
    _ = 2 * P * Z := by ring

/-- Product of absolute values over the chosen embeddings. When every complex
embedding is included, complex-conjugate pairs are counted twice. -/
def embeddingNormProduct {K ι : Type*} [CommRing K] [Fintype ι]
    (emb : ι → K →+* ℂ) (x : K) : ℝ := ∏ i, ‖emb i x‖

/-- A sufficiently small product of close-pair errors forces a determinant
to vanish, provided the arithmetic lattice has the stated norm separation. -/
theorem close_pair_determinant_eq_zero
    {K ι : Type*} [CommRing K] [Fintype ι]
    (emb : ι → K →+* ℂ) (Λ : Set K) (c : ℝ)
    (hlower : ∀ z ∈ Λ, z ≠ 0 → c ≤ embeddingNormProduct emb z)
    (θ : ι → ℂ) (P Z : ι → ℝ) (u₁ u₂ b₁ b₂ : K)
    (hmem : b₁ * u₂ - b₂ * u₁ ∈ Λ)
    (hZ : ∀ i, 0 ≤ Z i)
    (hu₁ : ∀ i, ‖emb i u₁‖ ≤ P i) (hu₂ : ∀ i, ‖emb i u₂‖ ≤ P i)
    (hb₁ : ∀ i, ‖emb i b₁ - θ i * emb i u₁‖ ≤ Z i)
    (hb₂ : ∀ i, ‖emb i b₂ - θ i * emb i u₂‖ ≤ Z i)
    (hsmall : (∏ i, 2 * P i * Z i) < c) :
    b₁ * u₂ - b₂ * u₁ = 0 := by
  have hupper : embeddingNormProduct emb (b₁ * u₂ - b₂ * u₁) ≤
      ∏ i, 2 * P i * Z i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      simpa only [map_sub, map_mul] using close_pair_determinant_norm_bound
        (θ i) (emb i u₁) (emb i u₂) (emb i b₁) (emb i b₂)
        (P i) (Z i) (hZ i) (hu₁ i) (hu₂ i) (hb₁ i) (hb₂ i)
  by_contra hne
  exact (not_lt_of_ge ((hlower _ hmem hne).trans hupper)) hsmall

end WaringSiegel
