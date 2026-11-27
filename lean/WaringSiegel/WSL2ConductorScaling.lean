import WaringSiegel.WSL2TraceMajorArcUnion
import WaringSiegel.WSL2IdealSummability

/-!
# WSL2: fixed integer multipliers in the conductor major arcs

Dividing a rational center by a positive integer k costs at most k^[K:Q]
in its conductor norm. This proves the precise major-arc inclusion needed
when differencing produces kθ, 6θ, or another fixed integer multiple.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem conductorIdeal_div_nat_mul_le (I : FractionalIdeal (𝓞 K)⁰ K)
    (γ : K) (k : ℕ) (hk : k ≠ 0) :
    Ideal.span ({(k : 𝓞 K)} : Set (𝓞 K)) * conductorIdeal I γ ≤
      conductorIdeal I (γ/(k:K)) := by
  apply Ideal.span_singleton_mul_le_iff.mpr
  intro a ha
  change (((k : 𝓞 K)*a : 𝓞 K) : K) * (γ/(k:K)) ∈ I
  have hkK : (k:K) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have he : (((k : 𝓞 K)*a : 𝓞 K) : K) * (γ/(k:K)) = (a:K)*γ := by
    push_cast
    field_simp
  rwa [he]

theorem conductorIdeal_div_nat_norm_le (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (γ : K) (k : ℕ) (hk : k ≠ 0) :
    Ideal.absNorm (conductorIdeal I (γ/(k:K))) ≤
      k^finrank ℚ K * Ideal.absNorm (conductorIdeal I γ) := by
  have hdiv := Ideal.absNorm_dvd_absNorm_of_le (conductorIdeal_div_nat_mul_le I γ k hk)
  rw [map_mul, ideal_absNorm_span_nat] at hdiv
  apply Nat.le_of_dvd _ hdiv
  exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero hk) _) (conductorIdeal_absNorm_pos I hI γ)

theorem productArcWeight_le_smul (H a : ℝ) (hH : 0 ≤ H) (ha : 1 ≤ a)
    (β : mixedSpace K) : productArcWeight H β ≤ productArcWeight H (a • β) := by
  apply Finset.prod_le_prod
  · intro w hw
    exact pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  · intro w hw
    rw [normAtPlace_smul, abs_of_nonneg (by linarith)]
    apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
    apply max_le_max_left
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (normAtPlace_nonneg _ _) ha) hH

theorem mixed_nat_smul_sub_div (θ : mixedSpace K) (γ : K) (k : ℕ) (hk : k ≠ 0) :
    (k:ℝ) • (θ-mixedEmbedding K (γ/(k:K))) =
      (k:ℝ) • θ-mixedEmbedding K γ := by
  rw [smul_sub]
  congr 1
  rw [Algebra.smul_def, map_natCast, ← map_natCast (mixedEmbedding K) k, ← map_mul]
  congr 1
  have hkK : (k:K) ≠ 0 := Nat.cast_ne_zero.mpr hk
  field_simp

/-- A major arc for kθ maps back into the major arcs for θ with cutoff
multiplied by k^degree. -/
theorem productMajorArc_smul_nat_preimage
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (H L : ℝ) (hH : 0 ≤ H) (θ : mixedSpace K) (γ : K)
    (k : ℕ) (hk : 0 < k)
    (hθ : (k:ℝ) • θ ∈ productMajorArc I H L γ) :
    θ ∈ productMajorArc I H ((k:ℝ)^finrank ℚ K * L) (γ/(k:K)) := by
  have hq : (Ideal.absNorm (conductorIdeal I (γ/(k:K))) : ℝ) ≤
      (k:ℝ)^finrank ℚ K * (Ideal.absNorm (conductorIdeal I γ) : ℝ) := by
    exact_mod_cast conductorIdeal_div_nat_norm_le I hI γ k hk.ne'
  have ha : productArcWeight H (θ-mixedEmbedding K (γ/(k:K))) ≤
      productArcWeight H ((k:ℝ) • θ-mixedEmbedding K γ) := by
    rw [← mixed_nat_smul_sub_div θ γ k hk.ne']
    exact productArcWeight_le_smul H k hH (by exact_mod_cast hk) _
  change (Ideal.absNorm (conductorIdeal I (γ/(k:K))) : ℝ) *
    productArcWeight H (θ-mixedEmbedding K (γ/(k:K))) ≤ _
  calc
    _ ≤ ((k:ℝ)^finrank ℚ K * (Ideal.absNorm (conductorIdeal I γ) : ℝ)) *
        productArcWeight H ((k:ℝ) • θ-mixedEmbedding K γ) :=
      mul_le_mul hq ha (productArcWeight_pos _ _).le (by positivity)
    _ = (k:ℝ)^finrank ℚ K * ((Ideal.absNorm (conductorIdeal I γ) : ℝ) *
        productArcWeight H ((k:ℝ) • θ-mixedEmbedding K γ)) := by ring
    _ ≤ (k:ℝ)^finrank ℚ K * L := mul_le_mul_of_nonneg_left hθ (by positivity)

/-- The literal minor-arc implication, including the multiplier in the cutoff. -/
theorem traceMajorArcUnion_smul_nat_preimage
    (H L : ℝ) (hH : 0 ≤ H) (θ : mixedSpace K) (k : ℕ) (hk : 0 < k)
    (hθ : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion H ((k:ℝ)^finrank ℚ K * L)) :
    ∀ γ : K, L < (Ideal.absNorm (traceConductor γ) : ℝ) *
      productArcWeight H ((k:ℝ) • θ-mixedEmbedding K γ) := by
  intro γ
  by_contra h
  apply hθ
  refine Set.mem_iUnion.mpr ⟨γ/(k:K), θ, ?_, rfl⟩
  exact productMajorArc_smul_nat_preimage _ inverseDifferent_ne_zero H L hH θ γ k hk
    (le_of_not_gt h)

end WaringSiegel
