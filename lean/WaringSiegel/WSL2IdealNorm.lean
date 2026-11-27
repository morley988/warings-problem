import WaringSiegel.NormLattice
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# WSL2: separation by the actual absolute ideal norm

The norm lower bound is now exactly the absolute norm of the fractional
ideal. This removes the denominator-dependent constant and is the uniform
arithmetic input for anisotropic packing over a varying ideal.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem ideal_absNorm_le_element_norm (I : Ideal (𝓞 K))
    {z : 𝓞 K} (hz : z ∈ I) (hz0 : z ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ absNorm z := by
  have hn : Algebra.norm ℤ z ≠ 0 := Algebra.norm_ne_zero_iff.mpr hz0
  have hd := Int.natAbs_le_of_dvd_ne_zero (Ideal.absNorm_dvd_norm_of_mem hz) hn
  simp only [Int.natAbs_natCast] at hd
  unfold absNorm
  have hreal : (Ideal.absNorm I : ℝ) ≤ ((Algebra.norm ℤ z).natAbs : ℝ) := by
    exact_mod_cast hd
  simpa only [Int.cast_natAbs, Int.cast_abs] using hreal

theorem fractionalIdeal_absNorm_pos (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) : (0 : ℝ) < FractionalIdeal.absNorm I := by
  have hnonneg := FractionalIdeal.absNorm_nonneg I
  have hne : FractionalIdeal.absNorm I ≠ 0 :=
    mt FractionalIdeal.absNorm_eq_zero_iff.mp hI
  exact_mod_cast lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Every nonzero member of an actual fractional ideal has absolute field
norm at least the actual absolute ideal norm, uniformly in the ideal. -/
theorem fractionalIdeal_absNorm_le_fieldAbsNorm
    (I : FractionalIdeal (𝓞 K)⁰ K) {z : K} (hz : z ∈ I) (hz0 : z ≠ 0) :
    (FractionalIdeal.absNorm I : ℝ) ≤ fieldAbsNorm z := by
  have hd : (I.den : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  let a : I.num := FractionalIdeal.equivNum hd ⟨z, hz⟩
  have ha : ((a : 𝓞 K) : K) = ((I.den : 𝓞 K) : K) * z := by
    have h := FractionalIdeal.equivNum_apply hd (⟨z, hz⟩ : I)
    simpa only [a, Submonoid.smul_def, Algebra.smul_def,
      NumberField.RingOfIntegers.coe_eq_algebraMap] using h
  have ha0 : (a : 𝓞 K) ≠ 0 := by
    intro h
    have hdK : ((I.den : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hd
    have : ((I.den : 𝓞 K) : K) * z = 0 := by simpa [h] using ha.symm
    exact mul_ne_zero hdK hz0 this
  have hlo := ideal_absNorm_le_element_norm I.num a.property ha0
  have hmul : absNorm (a : 𝓞 K) = absNorm (I.den : 𝓞 K) * fieldAbsNorm z := by
    rw [← fieldAbsNorm_integer, ha, fieldAbsNorm_mul, fieldAbsNorm_integer]
  have hdpos : 0 < absNorm (I.den : 𝓞 K) :=
    lt_of_lt_of_le zero_lt_one (one_le_absNorm_integer hd)
  rw [FractionalIdeal.absNorm_eq]
  push_cast
  change (Ideal.absNorm I.num : ℝ) / absNorm (I.den : 𝓞 K) ≤ fieldAbsNorm z
  apply (div_le_iff₀ hdpos).mpr
  simpa only [hmul, mul_comm] using hlo

/-- The same exact separation in the actual mixed archimedean space. -/
theorem fractionalIdeal_absNorm_le_mixed_norm
    (I : FractionalIdeal (𝓞 K)⁰ K) {z : K} (hz : z ∈ I) (hz0 : z ≠ 0) :
    (FractionalIdeal.absNorm I : ℝ) ≤
      NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K z) := by
  simpa only [NumberField.mixedEmbedding.norm_eq_norm, fieldAbsNorm,
    Rat.cast_abs] using fractionalIdeal_absNorm_le_fieldAbsNorm I hz hz0

end WaringSiegel
