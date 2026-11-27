import WaringSiegel.NumberFieldTargets
import WaringSiegel.NormSeparation
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Arithmetic norm separation in actual fractional ideals

An actual nonzero algebraic integer has absolute norm at least one. Clearing
a denominator supplies a uniform positive norm lower bound on every nonzero
element of a fractional ideal. This discharges the arithmetic lower-bound
premise in the elementary close-pair determinant argument.
-/

noncomputable section
open scoped NumberField BigOperators nonZeroDivisors

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def fieldAbsNorm (z : K) : ℝ := |(Algebra.norm ℚ z : ℝ)|

theorem fieldAbsNorm_mul (x y : K) : fieldAbsNorm (x * y) = fieldAbsNorm x * fieldAbsNorm y := by
  simp [fieldAbsNorm, map_mul, abs_mul]

theorem fieldAbsNorm_pos {z : K} (hz : z ≠ 0) : 0 < fieldAbsNorm z := by
  apply abs_pos.mpr
  have hn : Algebra.norm ℚ z ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz
  exact_mod_cast hn

theorem fieldAbsNorm_integer (z : 𝓞 K) : fieldAbsNorm (z : K) = absNorm z := by
  unfold fieldAbsNorm absNorm
  rw [← Algebra.coe_norm_int]
  norm_cast

theorem one_le_absNorm_integer {z : 𝓞 K} (hz : z ≠ 0) : 1 ≤ absNorm z := by
  have hn : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz
  have h := Int.one_le_abs hn
  unfold absNorm
  exact_mod_cast h

/-- Product over all complex embeddings, counting conjugate embeddings separately. -/
theorem embeddingNormProduct_eq_fieldAbsNorm (z : K) :
    embeddingNormProduct (fun σ : K →ₐ[ℚ] ℂ => σ.toRingHom) z = fieldAbsNorm z := by
  unfold embeddingNormProduct fieldAbsNorm
  change (∏ σ : K →ₐ[ℚ] ℂ, ‖σ z‖) = |(Algebra.norm ℚ z : ℝ)|
  rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]
  change ‖(Algebra.norm ℚ z : ℂ)‖ = |(Algebra.norm ℚ z : ℝ)|
  exact Complex.norm_ratCast _

/-- A fixed integral denominator gives a positive norm separation. -/
theorem fieldAbsNorm_lower_of_integral_multiple
    (d : 𝓞 K) (hd : d ≠ 0) {z : K} (hz : z ≠ 0)
    (hint : IsLocalization.IsInteger (𝓞 K) ((d : K) * z)) :
    1 / absNorm d ≤ fieldAbsNorm z := by
  obtain ⟨a, ha⟩ := hint
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have ha0 : a ≠ 0 := by
    intro haz
    have : (d : K) * z = 0 := by simpa [haz] using ha.symm
    exact mul_ne_zero hdK hz this
  have hnorm : fieldAbsNorm ((d : K) * z) = absNorm a := by
    rw [← ha]
    exact fieldAbsNorm_integer a
  have hlo : 1 ≤ absNorm d * fieldAbsNorm z := by
    rw [← fieldAbsNorm_integer d, ← fieldAbsNorm_mul, hnorm]
    exact one_le_absNorm_integer ha0
  apply (div_le_iff₀ ?_).mpr
  · simpa [mul_comm] using hlo
  · exact lt_of_lt_of_le zero_lt_one (one_le_absNorm_integer hd)

/-- Every actual fractional ideal has a positive lower norm bound for its
nonzero elements, with no assumption of a pre-existing lattice estimate. -/
theorem fractionalIdeal_norm_separation (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ I, z ≠ 0 →
      c ≤ embeddingNormProduct (fun σ : K →ₐ[ℚ] ℂ => σ.toRingHom) z := by
  obtain ⟨d, hd, hden⟩ := I.isFractional
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  refine ⟨1 / absNorm d, div_pos zero_lt_one ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (one_le_absNorm_integer hd0)
  · intro z hz hz0
    rw [embeddingNormProduct_eq_fieldAbsNorm]
    apply fieldAbsNorm_lower_of_integral_multiple d hd0 hz0
    simpa only [Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap] using hden z hz

/-- Applying norm separation to the actual fractional-ideal module containing
the determinants. The positive constant depends only on the chosen lattice. -/
theorem fractionalIdeal_close_pair_separation (I : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (θ : (K →ₐ[ℚ] ℂ) → ℂ) (P Z : (K →ₐ[ℚ] ℂ) → ℝ)
        (u₁ u₂ : 𝓞 K) (b₁ b₂ : K),
        b₁ ∈ I → b₂ ∈ I →
        (∀ σ, 0 ≤ Z σ) →
        (∀ σ, ‖σ (u₁ : K)‖ ≤ P σ) → (∀ σ, ‖σ (u₂ : K)‖ ≤ P σ) →
        (∀ σ, ‖σ b₁ - θ σ * σ (u₁ : K)‖ ≤ Z σ) →
        (∀ σ, ‖σ b₂ - θ σ * σ (u₂ : K)‖ ≤ Z σ) →
        (∏ σ, 2 * P σ * Z σ) < c → b₁ * (u₂ : K) - b₂ * (u₁ : K) = 0 := by
  obtain ⟨c, hc, hsep⟩ := fractionalIdeal_norm_separation I
  refine ⟨c, hc, ?_⟩
  intro θ P Z u₁ u₂ b₁ b₂ hb₁ hb₂ hZ hu₁ hu₂ h₁ h₂ hsmall
  have hmem : b₁ * (u₂ : K) - b₂ * (u₁ : K) ∈ I := by
    have hm₁ := (I : Submodule (𝓞 K) K).smul_mem u₂ hb₁
    have hm₂ := (I : Submodule (𝓞 K) K).smul_mem u₁ hb₂
    simpa only [Algebra.smul_def, NumberField.RingOfIntegers.coe_eq_algebraMap,
      mul_comm] using (I : Submodule (𝓞 K) K).sub_mem hm₁ hm₂
  exact close_pair_determinant_eq_zero
    (fun σ : K →ₐ[ℚ] ℂ => σ.toRingHom) (I : Set K) c hsep
    θ P Z (u₁ : K) (u₂ : K) b₁ b₂ hmem hZ hu₁ hu₂ h₁ h₂ hsmall

end WaringSiegel
