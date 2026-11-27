import WaringSiegel.WSL2ConductorSeparation

/-!
# WSL2: disjointness of actual conductor-defined product arcs

The arc weight is the literal product of max(1,H|β_v|), with the correct
local multiplicities. The separation theorem is uniform in all conductor
ideals and all archimedean aspect ratios.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

def productArcWeight (H : ℝ) (β : mixedSpace K) : ℝ :=
  ∏ w : InfinitePlace K, max 1 (H * normAtPlace w β) ^ mult w

theorem productArcWeight_one_le (H : ℝ) (β : mixedSpace K) : 1 ≤ productArcWeight H β := by
  calc
    (1 : ℝ) = ∏ _w : InfinitePlace K, (1 : ℝ) := by simp
    _ ≤ productArcWeight H β := Finset.prod_le_prod (fun _ _ => by norm_num)
      (fun w _ => one_le_pow₀ (le_max_left _ _))

theorem productArcWeight_pos (H : ℝ) (β : mixedSpace K) : 0 < productArcWeight H β :=
  lt_of_lt_of_le zero_lt_one (productArcWeight_one_le H β)

theorem productArcWeight_difference_norm (H : ℝ) (hH : 0 < H) (β₁ β₂ : mixedSpace K) :
    NumberField.mixedEmbedding.norm (β₁ - β₂) * H ^ finrank ℚ K ≤
      (2 : ℝ) ^ finrank ℚ K * productArcWeight H β₁ * productArcWeight H β₂ := by
  let A : InfinitePlace K → ℝ := fun w => max 1 (H * normAtPlace w β₁)
  let B : InfinitePlace K → ℝ := fun w => max 1 (H * normAtPlace w β₂)
  have hA : ∀ w, 1 ≤ A w := fun _ => le_max_left _ _
  have hB : ∀ w, 1 ≤ B w := fun _ => le_max_left _ _
  have hlocal : ∀ w, normAtPlace w (H • (β₁ - β₂)) ≤ 2 * (A w * B w) := by
    intro w
    rw [normAtPlace_smul, abs_of_pos hH]
    have ht := mul_le_mul_of_nonneg_left (normAtPlace_sub_le w β₁ β₂) hH.le
    have h₁ : H * normAtPlace w β₁ ≤ A w := le_max_right _ _
    have h₂ : H * normAtPlace w β₂ ≤ B w := le_max_right _ _
    have h₃ : A w ≤ A w * B w := le_mul_of_one_le_right (by linarith [hA w]) (hB w)
    have h₄ : B w ≤ A w * B w := le_mul_of_one_le_left (by linarith [hB w]) (hA w)
    nlinarith
  have hp := mixed_productNorm_le_scaled_radii (H • (β₁ - β₂)) 2 (by norm_num)
    (fun w => A w * B w) (fun w => mul_nonneg (by linarith [hA w]) (by linarith [hB w])) hlocal
  rw [NumberField.mixedEmbedding.norm_smul, abs_of_pos hH] at hp
  simp only [mul_pow, Finset.prod_mul_distrib] at hp
  simpa only [productArcWeight, A, B, mul_assoc, mul_comm, mul_left_comm] using hp

def productMajorArc (I : FractionalIdeal (𝓞 K)⁰ K) (H L : ℝ) (γ : K) : Set (mixedSpace K) :=
  {θ | (Ideal.absNorm (conductorIdeal I γ) : ℝ) *
    productArcWeight H (θ - mixedEmbedding K γ) ≤ L}

/-- If `2^d L² < N(I) H^d`, no point lies in product arcs about two
different field centers. This also proves uniqueness of a lifted center. -/
theorem productMajorArcs_disjoint
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ) ^ finrank ℚ K * L ^ 2 <
      (FractionalIdeal.absNorm I : ℝ) * H ^ finrank ℚ K)
    (γ δ : K) (hne : γ ≠ δ) :
    Disjoint (productMajorArc I H L γ) (productMajorArc I H L δ) := by
  rw [Set.disjoint_left]
  intro θ hγ hδ
  let Q₁ : ℝ := Ideal.absNorm (conductorIdeal I γ)
  let Q₂ : ℝ := Ideal.absNorm (conductorIdeal I δ)
  let A := productArcWeight H (θ - mixedEmbedding K γ)
  let B := productArcWeight H (θ - mixedEmbedding K δ)
  have hQ₁ : 0 < Q₁ := by
    dsimp [Q₁]
    exact_mod_cast conductorIdeal_absNorm_pos I hI γ
  have hQ₂ : 0 < Q₂ := by
    dsimp [Q₂]
    exact_mod_cast conductorIdeal_absNorm_pos I hI δ
  have hA : 0 ≤ A := (productArcWeight_pos _ _).le
  have hB : 0 ≤ B := (productArcWeight_pos _ _).le
  have hlo := conductor_difference_norm_lower I hI γ δ hne
  change (FractionalIdeal.absNorm I : ℝ) / (Q₁ * Q₂) ≤ fieldAbsNorm (γ - δ) at hlo
  have hlo' := (div_le_iff₀ (mul_pos hQ₁ hQ₂)).mp hlo
  have hhi := productArcWeight_difference_norm H hH
    (θ - mixedEmbedding K δ) (θ - mixedEmbedding K γ)
  have heq : (θ - mixedEmbedding K δ) - (θ - mixedEmbedding K γ) =
      mixedEmbedding K (γ - δ) := by rw [map_sub]; ring
  rw [heq, NumberField.mixedEmbedding.norm_eq_norm] at hhi
  rw [Rat.cast_abs] at hhi
  change fieldAbsNorm (γ - δ) * H ^ finrank ℚ K ≤ (2 : ℝ) ^ finrank ℚ K * B * A at hhi
  have hcut : Q₁ * A * (Q₂ * B) ≤ L * L :=
    mul_le_mul hγ hδ (mul_nonneg hQ₂.le hB) hL
  have hpos2 : 0 ≤ (2 : ℝ) ^ finrank ℚ K := by positivity
  have hHp : 0 ≤ H ^ finrank ℚ K := (pow_pos hH _).le
  have hfinal : (FractionalIdeal.absNorm I : ℝ) * H ^ finrank ℚ K ≤
      (2 : ℝ) ^ finrank ℚ K * L ^ 2 := by
    calc
      _ ≤ (fieldAbsNorm (γ - δ) * (Q₁ * Q₂)) * H ^ finrank ℚ K :=
        mul_le_mul_of_nonneg_right hlo' hHp
      _ = (fieldAbsNorm (γ - δ) * H ^ finrank ℚ K) * (Q₁ * Q₂) := by ring
      _ ≤ ((2 : ℝ) ^ finrank ℚ K * B * A) * (Q₁ * Q₂) :=
        mul_le_mul_of_nonneg_right hhi (mul_pos hQ₁ hQ₂).le
      _ = (2 : ℝ) ^ finrank ℚ K * (Q₁ * A * (Q₂ * B)) := by ring
      _ ≤ (2 : ℝ) ^ finrank ℚ K * (L * L) := mul_le_mul_of_nonneg_left hcut hpos2
      _ = _ := by rw [pow_two]
  exact (not_le_of_gt hsmall) hfinal

end WaringSiegel
