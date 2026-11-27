import WaringSiegel.WSL3CubicFiniteSharp
import WaringSiegel.WSL2LocalOriginalDensity

/-! # WSL3: target-uniform cubic local-density error of order q⁻³

The singular recurrence is the exact WSL2 recurrence.  The new input is the
Gauss-sum finite-field bound; no uniformity premise on the target is assumed.
-/
noncomputable section
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel
variable {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]

def cubicPrimitiveSharpErrorBound (R : Type*) [CommRing R] [IsLocalRing R] : ℝ :=
  256 / (Nat.card (ResidueField R) : ℝ) ^ 3 +
    1 / (Nat.card (ResidueField R) : ℝ) ^ 7

theorem cubicPrimitiveSharpErrorBound_nonneg : 0 ≤ cubicPrimitiveSharpErrorBound R := by
  unfold cubicPrimitiveSharpErrorBound
  positivity

/-- Primitive density is within the explicit finite-field error plus `q^-7`
of 1, uniformly in the target. -/
theorem primitive_eight_density_bounds_sharp
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) :
    0 ≤ primitiveEightCubicDensity R a ∧
      1 - cubicPrimitiveSharpErrorBound R ≤ primitiveEightCubicDensity R a ∧
      primitiveEightCubicDensity R a ≤ 1 + cubicPrimitiveSharpErrorBound R := by
  letI := Fintype.ofFinite (ResidueField R)
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hpow : 0 < (Nat.card (ResidueField R) : ℝ) ^ 7 := pow_pos hq _
  have hfull := finite_field_eight_cubes_normalized_error_sharp (residue R a)
  rw [← Nat.card_eq_fintype_card] at hfull
  have hlo : (finiteFieldCubicSolutionCount (ResidueField R) 8 (residue R a) : ℝ) ≤
      (Nat.card (PrimitiveCubicResidues R 8 a) : ℝ) + 1 := by
    exact_mod_cast full_cube_residue_count_le_primitive_add_one 8 a
  have hhi : (Nat.card (PrimitiveCubicResidues R 8 a) : ℝ) ≤
      (finiteFieldCubicSolutionCount (ResidueField R) 8 (residue R a) : ℝ) := by
    exact_mod_cast primitive_cube_residue_count_le_full 8 a
  have hlo' := div_le_div_of_nonneg_right hlo hpow.le
  have hhi' := div_le_div_of_nonneg_right hhi hpow.le
  rw [add_div] at hlo'
  obtain ⟨hminus, hplus⟩ := abs_le.mp hfull
  unfold primitiveEightCubicDensity cubicPrimitiveSharpErrorBound
  refine ⟨div_nonneg (Nat.cast_nonneg _) hpow.le, ?_, ?_⟩
  · linarith
  · have hsmall : 0 ≤ 1 / (Nat.card (ResidueField R) : ℝ) ^ 7 := by positivity
    linarith

def cubicDensitySharpUpperBound (R : Type*) [CommRing R] [IsLocalRing R] : ℝ :=
  (1 + cubicPrimitiveSharpErrorBound R) / (1 - 1 / (Nat.card (ResidueField R) : ℝ) ^ 5)

theorem cubicDensitySharpUpperBound_nonneg : 0 ≤ cubicDensitySharpUpperBound R := by
  unfold cubicDensitySharpUpperBound
  exact div_nonneg (by have := cubicPrimitiveSharpErrorBound_nonneg (R := R); linarith)
    (sub_pos.mpr (cubic_singular_ratio_lt_one (R := R))).le

theorem cubicDensitySharpUpperBound_fixed_point :
    1 + cubicPrimitiveSharpErrorBound R +
      cubicDensitySharpUpperBound R / (Nat.card (ResidueField R) : ℝ) ^ 5 =
        cubicDensitySharpUpperBound R := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hd : 1 - 1 / (Nat.card (ResidueField R) : ℝ) ^ 5 ≠ 0 :=
    (sub_pos.mpr (cubic_singular_ratio_lt_one (R := R))).ne'
  have hmul : cubicDensitySharpUpperBound R * (1 - 1 / (Nat.card (ResidueField R) : ℝ) ^ 5) =
      1 + cubicPrimitiveSharpErrorBound R := by
    unfold cubicDensitySharpUpperBound
    exact div_mul_cancel₀ _ hd
  rw [div_eq_mul_one_div]
  nlinarith

theorem one_add_primitive_error_le_density_sharp_upper :
    1 + cubicPrimitiveSharpErrorBound R ≤ cubicDensitySharpUpperBound R := by
  rw [← cubicDensitySharpUpperBound_fixed_point (R := R)]
  exact le_add_of_nonneg_right (div_nonneg (cubicDensitySharpUpperBound_nonneg (R := R)) (by positivity))

/-- A uniform real estimate for the singular geometric tail. -/
theorem cubic_density_upper_error_le_inv_cube (q : ℝ) (hq : 2 ≤ q) :
    (1 + (256 / q^3 + 1 / q^7)) / (1 - 1 / q^5) - 1 ≤ 516 / q^3 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hpow5 : 32 ≤ q^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq 5
    norm_num at h
    exact h
  have hr0 : 0 ≤ 1 / q^5 := by positivity
  have hrhalf : 1 / q^5 ≤ 1 / 2 := by
    calc
      1 / q^5 ≤ 1 / (32 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpow5
      _ ≤ 1 / 2 := by norm_num
  have hden : 0 < 1 - 1 / q^5 := by linarith
  have h5 : 1 / q^5 ≤ 1 / q^3 := one_div_le_one_div_of_le (pow_pos hq0 3)
    (pow_le_pow_right₀ hq1 (by decide : 3 ≤ 5))
  have h7 : 1 / q^7 ≤ 1 / q^3 := one_div_le_one_div_of_le (pow_pos hq0 3)
    (pow_le_pow_right₀ hq1 (by decide : 3 ≤ 7))
  let B := 256 / q^3 + 1 / q^7
  let U := (1 + B) / (1 - 1 / q^5)
  have hU : 1 ≤ U := by
    apply (le_div_iff₀ hden).mpr
    dsimp [B]
    have : 0 ≤ 256 / q^3 + 1 / q^7 := by positivity
    linarith
  have hmul : U * (1 - 1 / q^5) = 1 + B := div_mul_cancel₀ _ hden.ne'
  have hrel : (U - 1) * (1 - 1 / q^5) = B + 1 / q^5 := by nlinarith
  have hprod : 0 ≤ (U - 1) * ((1 - 1 / q^5) - 1 / 2) :=
    mul_nonneg (sub_nonneg.mpr hU) (by linarith)
  have hfirst : U - 1 ≤ 2 * (B + 1 / q^5) := by nlinarith
  have hsecond : B + 1 / q^5 ≤ 258 / q^3 := by
    calc
      B + 1 / q^5 ≤ (256 / q^3 + 1 / q^3) + 1 / q^3 :=
        add_le_add (add_le_add_left h7 _) h5
      _ = _ := by ring
  change U - 1 ≤ _
  calc
    U - 1 ≤ 2 * (B + 1 / q^5) := hfirst
    _ ≤ 2 * (258 / q^3) := mul_le_mul_of_nonneg_left hsecond (by norm_num)
    _ = _ := by ring

theorem cubicDensitySharpUpperBound_error_le_inv_cube :
    cubicDensitySharpUpperBound R - 1 ≤ 516 / (Nat.card (ResidueField R) : ℝ)^3 := by
  apply cubic_density_upper_error_le_inv_cube
  letI := Fintype.ofFinite (ResidueField R)
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast (show 2 ≤ Fintype.card (ResidueField R) from Fintype.one_lt_card)

section DVR
variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]

theorem good_prime_cubic_unit_pow_bounded_limit_sharp
    (h6 : (6 : ResidueField R) ≠ 0) {π : R} (hπ : Irreducible π) (u : Rˣ) (k : ℕ) :
    ∃ σ : ℝ, (0 ≤ σ ∧ 1 - cubicPrimitiveSharpErrorBound R ≤ σ ∧ σ ≤ cubicDensitySharpUpperBound R) ∧
      ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
        normalizedLocalCubicCount R 8 e ((u : R) * π ^ k) = σ := by
  have h3 := three_isUnit_of_six_residue_ne_zero h6
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨hP0, hPl, hPu⟩ := primitive_eight_density_bounds_sharp h6 ((u : R) * π ^ k)
    by_cases hk : k < 3
    · refine ⟨primitiveEightCubicDensity R ((u : R) * π ^ k),
        ⟨hP0, hPl, hPu.trans (one_add_primitive_error_le_density_sharp_upper (R := R))⟩, 3, ?_⟩
      intro e he
      have heq : e = (e - 3) + 3 := (Nat.sub_add_cancel he).symm
      rw [heq]
      exact normalized_cubic_count_eq_of_not_mem_cube_ideal h3 (e - 3)
        (unit_mul_uniformizer_pow_not_mem_cube_ideal hπ u hk)
    · have hk3 : 3 ≤ k := Nat.le_of_not_gt hk
      obtain ⟨σ, ⟨hσ0, -, hσu⟩, E, hE⟩ := ih (k - 3) (by omega)
      have ha : (u : R) * π ^ k = π ^ 3 * ((u : R) * π ^ (k - 3)) := by
        calc
          (u : R) * π ^ k = (u : R) * (π ^ (k - 3) * π ^ 3) := by
            rw [← pow_add, Nat.sub_add_cancel hk3]
          _ = π ^ 3 * ((u : R) * π ^ (k - 3)) := by ring
      let σ' := primitiveEightCubicDensity R ((u : R) * π ^ k) +
        σ / (Nat.card (ResidueField R) : ℝ) ^ 5
      have hσd0 : 0 ≤ σ / (Nat.card (ResidueField R) : ℝ) ^ 5 := div_nonneg hσ0 (pow_pos hq _).le
      refine ⟨σ', ⟨add_nonneg hP0 hσd0, hPl.trans (le_add_of_nonneg_right hσd0), ?_⟩, E + 3, ?_⟩
      · calc
          σ' ≤ 1 + cubicPrimitiveSharpErrorBound R +
              cubicDensitySharpUpperBound R / (Nat.card (ResidueField R) : ℝ) ^ 5 :=
            add_le_add hPu (div_le_div_of_nonneg_right hσu (pow_pos hq _).le)
          _ = cubicDensitySharpUpperBound R := cubicDensitySharpUpperBound_fixed_point
      · intro e he
        have heq : e = (e - 3) + 3 := by omega
        dsimp [σ']
        rw [heq, ha, normalized_cubic_count_scaling_recurrence h3 hπ,
          hE (e - 3) (by omega)]

/-- Uniform bounds on the actual full local density, including nonunit targets. -/
theorem good_prime_cubic_density_bounds_sharp
    (h6 : (6 : ResidueField R) ≠ 0) {a : R} (ha : a ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount R 8 e a) atTop (𝓝 σ)) :
    0 ≤ σ ∧ 1 - cubicPrimitiveSharpErrorBound R ≤ σ ∧ σ ≤ cubicDensitySharpUpperBound R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨σ', hσ', E, hE⟩ := good_prime_cubic_unit_pow_bounded_limit_sharp h6 hπ u k
  have hlim' : Tendsto (fun e => normalizedLocalCubicCount R 8 e ((u : R) * π ^ k))
      atTop (𝓝 σ') := by
    apply Tendsto.congr' _ tendsto_const_nhds
    exact eventually_atTop.mpr ⟨E, fun e he => (hE e he).symm⟩
  have hσ : σ = σ' := tendsto_nhds_unique hlim hlim'
  exact hσ ▸ hσ'

/-- The full density has the manuscript's target-uniform `O(q⁻³)` error. -/
theorem good_prime_cubic_density_error_abs_sharp
    (h6 : (6 : ResidueField R) ≠ 0) {a : R} (ha : a ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount R 8 e a) atTop (𝓝 σ)) :
    |σ - 1| ≤ 516 / (Nat.card (ResidueField R) : ℝ)^3 := by
  obtain ⟨-, hlo, hhi⟩ := good_prime_cubic_density_bounds_sharp h6 ha hlim
  have hU := one_add_primitive_error_le_density_sharp_upper (R := R)
  have habs : |σ - 1| ≤ cubicDensitySharpUpperBound R - 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  exact habs.trans (cubicDensitySharpUpperBound_error_le_inv_cube (R := R))

end DVR

variable {K : Type*} [Field K] [NumberField K]

theorem completion_good_prime_cubic_density_error_abs_sharp
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    {ν : 𝓞 K} (hν0 : ν ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 σ)) :
    |σ - 1| ≤ 516 / (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ)^3 := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  have ha0 : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ≠ 0 := by
    intro h
    apply hν0
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  exact good_prime_cubic_density_error_abs_sharp h6 ha0 hlim

theorem original_good_prime_cubic_density_error_abs_sharp
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) {ν : 𝓞 K} (hν0 : ν ≠ 0)
    {σ : ℝ} (hlim : Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
      atTop (𝓝 σ)) :
    |σ - 1| ≤ 516 / (Ideal.absNorm v.asIdeal : ℝ)^3 := by
  have h6' : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    fun h => h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hlim' := hlim
  simp only [normalizedPrimePowerCubicCount_eq_completion] at hlim'
  simpa only [completion_residue_card_eq_absNorm] using
    completion_good_prime_cubic_density_error_abs_sharp v h6' hν0 hlim'

end WaringSiegel

#print axioms WaringSiegel.original_good_prime_cubic_density_error_abs_sharp
