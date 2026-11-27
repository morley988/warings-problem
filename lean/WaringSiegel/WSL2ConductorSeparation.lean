import WaringSiegel.WSL2Conductor

/-!
# WSL2: exact conductor-norm separation of rational centers

The lower bound uses the product of conductor norms, not the degree-th
power of an auxiliary integer denominator. This is the uniform number-field
separation required for the product major arcs.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem fractionalIdeal_absNorm_antitone
    (I J : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) (hJI : J ≤ I) :
    (FractionalIdeal.absNorm I : ℝ) ≤ (FractionalIdeal.absNorm J : ℝ) := by
  have hmul : J * I⁻¹ ≤ 1 := by
    simpa only [mul_inv_cancel₀ hI] using FractionalIdeal.mul_right_mono I⁻¹ hJI
  obtain ⟨A, hA⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hmul
  have hA0 : A ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp (by
    rw [hA]
    exact mul_ne_zero hJ (inv_ne_zero hI))
  have hnat : 1 ≤ Ideal.absNorm A := Nat.one_le_iff_ne_zero.mpr
    (mt Ideal.absNorm_eq_zero_iff.mp hA0)
  have hnorm : (1 : ℝ) ≤ (FractionalIdeal.absNorm (J * I⁻¹) : ℝ) := by
    rw [← hA, FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast hnat
  rw [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, ← div_eq_mul_inv] at hnorm
  exact (one_le_div (fractionalIdeal_absNorm_pos I hI)).mp hnorm

theorem conductor_difference_mul_le
    (I : FractionalIdeal (𝓞 K)⁰ K) (γ δ : K) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ - δ) *
      ((conductorIdeal I γ : FractionalIdeal (𝓞 K)⁰ K) *
        (conductorIdeal I δ : FractionalIdeal (𝓞 K)⁰ K)) ≤ I := by
  apply FractionalIdeal.spanSingleton_mul_le_iff.mpr
  intro z hz
  refine FractionalIdeal.mul_induction_on hz ?_ ?_
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    have h₁ := (I : Submodule (𝓞 K) K).smul_mem b ha
    have h₂ := (I : Submodule (𝓞 K) K).smul_mem a hb
    have h := (I : Submodule (𝓞 K) K).sub_mem h₁ h₂
    change (γ - δ) * ((a : K) * (b : K)) ∈ I
    convert h using 1 <;> simp only [Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] <;> ring
  · intro x y hx hy
    simpa only [mul_add] using (I : Submodule (𝓞 K) K).add_mem hx hy

/-- Every two distinct rational centers have the exact ideal-norm
separation used in disjointness of product major arcs. -/
theorem conductor_difference_norm_lower
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (γ δ : K) (hne : γ ≠ δ) :
    (FractionalIdeal.absNorm I : ℝ) /
        ((Ideal.absNorm (conductorIdeal I γ) : ℝ) *
          (Ideal.absNorm (conductorIdeal I δ) : ℝ)) ≤ fieldAbsNorm (γ - δ) := by
  let A : FractionalIdeal (𝓞 K)⁰ K := conductorIdeal I γ
  let B : FractionalIdeal (𝓞 K)⁰ K := conductorIdeal I δ
  have hA : A ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr (conductorIdeal_ne_zero I hI γ)
  have hB : B ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr (conductorIdeal_ne_zero I hI δ)
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ - δ) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have h := fractionalIdeal_absNorm_antitone I
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ - δ) * (A * B)) hI
    (mul_ne_zero hspan (mul_ne_zero hA hB)) (conductor_difference_mul_le I γ δ)
  have hpos : (0 : ℝ) < (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
      (Ideal.absNorm (conductorIdeal I δ) : ℝ) := by
    exact mul_pos (by exact_mod_cast conductorIdeal_absNorm_pos I hI γ)
      (by exact_mod_cast conductorIdeal_absNorm_pos I hI δ)
  apply (div_le_iff₀ hpos).mpr
  simpa only [A, B, map_mul, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_abs, fieldAbsNorm] using h

theorem traceConductor_difference_norm_lower (γ δ : K) (hne : γ ≠ δ) :
    (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) /
        ((Ideal.absNorm (traceConductor γ) : ℝ) * (Ideal.absNorm (traceConductor δ) : ℝ)) ≤
      fieldAbsNorm (γ - δ) :=
  conductor_difference_norm_lower _ inverseDifferent_ne_zero γ δ hne

end WaringSiegel
