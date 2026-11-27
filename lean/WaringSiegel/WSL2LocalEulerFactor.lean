import WaringSiegel.WSL2LocalFiniteFourier
import WaringSiegel.WSL2LocalAllPrimeTargets

/-!
# Uniform good-prime local density factors

The finite-field estimate controls primitive local density. The exact
singular scaling ratio `q^-5` then makes the full-density error uniform in
the nonzero target, including targets divisible by the finite prime.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped BigOperators Classical

namespace WaringSiegel

variable {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]

theorem primitive_cube_residue_count_le_full (s : ℕ) (a : R) :
    Nat.card (PrimitiveCubicResidues R s a) ≤
      finiteFieldCubicSolutionCount (ResidueField R) s (residue R a) := by
  unfold finiteFieldCubicSolutionCount
  apply Nat.card_le_card_of_injective
    (f := fun x : PrimitiveCubicResidues R s a => ⟨x.val, x.property.1⟩)
  intro x y h
  exact Subtype.ext (congrArg (fun z : {x : Fin s → ResidueField R //
    (∑ i, x i ^ 3) = residue R a} => z.val) h)

theorem full_cube_residue_count_le_primitive_add_one (s : ℕ) (a : R) :
    finiteFieldCubicSolutionCount (ResidueField R) s (residue R a) ≤
      Nat.card (PrimitiveCubicResidues R s a) + 1 := by
  let g : {x : Fin s → ResidueField R // (∑ i, x i ^ 3) = residue R a} →
      Option (PrimitiveCubicResidues R s a) := fun x =>
    if h : ∃ i, x.val i ≠ 0 then some ⟨x.val, x.property, h⟩ else none
  have hg : Function.Injective g := by
    intro x y hxy
    dsimp [g] at hxy
    by_cases hx : ∃ i, x.val i ≠ 0 <;> by_cases hy : ∃ i, y.val i ≠ 0
    · simp only [dif_pos hx, dif_pos hy] at hxy
      have he : (⟨x.val, x.property, hx⟩ : PrimitiveCubicResidues R s a) =
          ⟨y.val, y.property, hy⟩ := Option.some.inj hxy
      exact Subtype.ext (congrArg (fun z : PrimitiveCubicResidues R s a => z.val) he)
    · simp only [dif_pos hx, dif_neg hy] at hxy
      cases hxy
    · simp only [dif_neg hx, dif_pos hy] at hxy
      cases hxy
    · have hx0 : ∀ i, x.val i = 0 := by simpa only [not_exists, not_not] using hx
      have hy0 : ∀ i, y.val i = 0 := by simpa only [not_exists, not_not] using hy
      exact Subtype.ext (funext (fun i => (hx0 i).trans (hy0 i).symm))
  have h := Nat.card_le_card_of_injective g hg
  letI := Fintype.ofFinite (ResidueField R)
  letI := Fintype.ofFinite (PrimitiveCubicResidues R s a)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option,
    finiteFieldCubicSolutionCount] using h

def cubicPrimitiveErrorBound (R : Type*) [CommRing R] [IsLocalRing R] : ℝ :=
  Real.sqrt (72 / (Nat.card (ResidueField R) : ℝ) ^ 3) +
    1 / (Nat.card (ResidueField R) : ℝ) ^ 7

theorem cubicPrimitiveErrorBound_nonneg : 0 ≤ cubicPrimitiveErrorBound R := by
  unfold cubicPrimitiveErrorBound
  positivity

/-- Primitive density is within the explicit finite-field error plus `q^-7`
of 1, uniformly in the target. -/
theorem primitive_eight_density_bounds
    (h6 : (6 : ResidueField R) ≠ 0) (a : R) :
    0 ≤ primitiveEightCubicDensity R a ∧
      1 - cubicPrimitiveErrorBound R ≤ primitiveEightCubicDensity R a ∧
      primitiveEightCubicDensity R a ≤ 1 + cubicPrimitiveErrorBound R := by
  letI := Fintype.ofFinite (ResidueField R)
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hpow : 0 < (Nat.card (ResidueField R) : ℝ) ^ 7 := pow_pos hq _
  have hfull := finite_field_eight_cubes_normalized_error_abs h6 (residue R a)
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
  unfold primitiveEightCubicDensity cubicPrimitiveErrorBound
  refine ⟨div_nonneg (Nat.cast_nonneg _) hpow.le, ?_, ?_⟩
  · linarith
  · have hsmall : 0 ≤ 1 / (Nat.card (ResidueField R) : ℝ) ^ 7 := by positivity
    linarith

def cubicDensityUpperBound (R : Type*) [CommRing R] [IsLocalRing R] : ℝ :=
  (1 + cubicPrimitiveErrorBound R) / (1 - 1 / (Nat.card (ResidueField R) : ℝ) ^ 5)

theorem residue_card_real_one_lt : 1 < (Nat.card (ResidueField R) : ℝ) := by
  letI := Fintype.ofFinite (ResidueField R)
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.one_lt_card

theorem cubic_singular_ratio_lt_one : 1 / (Nat.card (ResidueField R) : ℝ) ^ 5 < 1 := by
  have hq := residue_card_real_one_lt (R := R)
  exact (div_lt_one (pow_pos (lt_trans zero_lt_one hq) 5)).mpr
    (one_lt_pow₀ hq (by decide))

theorem cubicDensityUpperBound_nonneg : 0 ≤ cubicDensityUpperBound R := by
  unfold cubicDensityUpperBound
  exact div_nonneg (by have := cubicPrimitiveErrorBound_nonneg (R := R); linarith)
    (sub_pos.mpr (cubic_singular_ratio_lt_one (R := R))).le

theorem cubicDensityUpperBound_fixed_point :
    1 + cubicPrimitiveErrorBound R +
      cubicDensityUpperBound R / (Nat.card (ResidueField R) : ℝ) ^ 5 =
        cubicDensityUpperBound R := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hd : 1 - 1 / (Nat.card (ResidueField R) : ℝ) ^ 5 ≠ 0 :=
    (sub_pos.mpr (cubic_singular_ratio_lt_one (R := R))).ne'
  have hmul : cubicDensityUpperBound R * (1 - 1 / (Nat.card (ResidueField R) : ℝ) ^ 5) =
      1 + cubicPrimitiveErrorBound R := by
    unfold cubicDensityUpperBound
    exact div_mul_cancel₀ _ hd
  rw [div_eq_mul_one_div]
  nlinarith

theorem one_add_primitive_error_le_density_upper :
    1 + cubicPrimitiveErrorBound R ≤ cubicDensityUpperBound R := by
  rw [← cubicDensityUpperBound_fixed_point (R := R)]
  exact le_add_of_nonneg_right (div_nonneg (cubicDensityUpperBound_nonneg (R := R)) (by positivity))

/-- Elementary real estimate for the geometric singular tail. -/
theorem cubic_density_upper_error_le_sqrt (q : ℝ) (hq : 2 ≤ q) :
    (1 + (Real.sqrt (72 / q ^ 3) + 1 / q ^ 7)) / (1 - 1 / q ^ 5) - 1 ≤
      24 / Real.sqrt (q ^ 3) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hd : 0 < Real.sqrt (q ^ 3) := Real.sqrt_pos.mpr (pow_pos hq0 _)
  have hpow5 : 32 ≤ q ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hq 5
    norm_num at h
    exact h
  have hr0 : 0 ≤ 1 / q ^ 5 := by positivity
  have hrhalf : 1 / q ^ 5 ≤ 1 / 2 := by
    calc
      1 / q ^ 5 ≤ 1 / (32 : ℝ) := one_div_le_one_div_of_le (by norm_num) hpow5
      _ ≤ 1 / 2 := by norm_num
  have hden : 0 < 1 - 1 / q ^ 5 := by linarith
  have hd5 : Real.sqrt (q ^ 3) ≤ q ^ 5 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(pow_pos hq0 _).le, ?_⟩
    rw [← pow_mul]
    exact pow_le_pow_right₀ hq1 (by decide : 3 ≤ 5 * 2)
  have hd7 : Real.sqrt (q ^ 3) ≤ q ^ 7 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(pow_pos hq0 _).le, ?_⟩
    rw [← pow_mul]
    exact pow_le_pow_right₀ hq1 (by decide : 3 ≤ 7 * 2)
  have h5 := one_div_le_one_div_of_le hd hd5
  have h7 := one_div_le_one_div_of_le hd hd7
  have hsqrt : Real.sqrt (72 / q ^ 3) ≤ 10 / Real.sqrt (q ^ 3) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 72)]
    apply div_le_div_of_nonneg_right _ hd.le
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  let B := Real.sqrt (72 / q ^ 3) + 1 / q ^ 7
  let U := (1 + B) / (1 - 1 / q ^ 5)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hU : 1 ≤ U := by
    apply (le_div_iff₀ hden).mpr
    dsimp [B]
    nlinarith [Real.sqrt_nonneg (72 / q ^ 3), show 0 ≤ 1 / q ^ 7 by positivity]
  have hmul : U * (1 - 1 / q ^ 5) = 1 + B := div_mul_cancel₀ _ hden.ne'
  have hrel : (U - 1) * (1 - 1 / q ^ 5) = B + 1 / q ^ 5 := by nlinarith
  have hprod : 0 ≤ (U - 1) * ((1 - 1 / q ^ 5) - 1 / 2) :=
    mul_nonneg (sub_nonneg.mpr hU) (by linarith)
  have hfirst : U - 1 ≤ 2 * (B + 1 / q ^ 5) := by nlinarith
  have hsecond : B + 1 / q ^ 5 ≤ 12 / Real.sqrt (q ^ 3) := by
    calc
      B + 1 / q ^ 5 ≤ (10 / Real.sqrt (q ^ 3) + 1 / Real.sqrt (q ^ 3)) +
          1 / Real.sqrt (q ^ 3) := add_le_add (add_le_add hsqrt h7) h5
      _ = 12 / Real.sqrt (q ^ 3) := by ring
  change U - 1 ≤ _
  calc
    U - 1 ≤ 2 * (B + 1 / q ^ 5) := hfirst
    _ ≤ 2 * (12 / Real.sqrt (q ^ 3)) := mul_le_mul_of_nonneg_left hsecond (by norm_num)
    _ = 24 / Real.sqrt (q ^ 3) := by ring

theorem cubicDensityUpperBound_error_le_sqrt :
    cubicDensityUpperBound R - 1 ≤ 24 / Real.sqrt ((Nat.card (ResidueField R) : ℝ) ^ 3) := by
  apply cubic_density_upper_error_le_sqrt
  letI := Fintype.ofFinite (ResidueField R)
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast (show 2 ≤ Fintype.card (ResidueField R) from Fintype.one_lt_card)

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]

theorem three_isUnit_of_six_residue_ne_zero (h6 : (6 : ResidueField R) ≠ 0) :
    IsUnit (3 : R) := by
  apply (residue_ne_zero_iff_isUnit (3 : R)).mp
  simp only [map_ofNat]
  intro h
  apply h6
  calc
    (6 : ResidueField R) = 2 * 3 := by ring
    _ = 0 := by rw [h, mul_zero]

theorem good_prime_cubic_unit_pow_bounded_limit
    (h6 : (6 : ResidueField R) ≠ 0) {π : R} (hπ : Irreducible π) (u : Rˣ) (k : ℕ) :
    ∃ σ : ℝ, (0 ≤ σ ∧ 1 - cubicPrimitiveErrorBound R ≤ σ ∧ σ ≤ cubicDensityUpperBound R) ∧
      ∃ E : ℕ, ∀ e : ℕ, E ≤ e →
        normalizedLocalCubicCount R 8 e ((u : R) * π ^ k) = σ := by
  have h3 := three_isUnit_of_six_residue_ne_zero h6
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨hP0, hPl, hPu⟩ := primitive_eight_density_bounds h6 ((u : R) * π ^ k)
    by_cases hk : k < 3
    · refine ⟨primitiveEightCubicDensity R ((u : R) * π ^ k),
        ⟨hP0, hPl, hPu.trans (one_add_primitive_error_le_density_upper (R := R))⟩, 3, ?_⟩
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
          σ' ≤ 1 + cubicPrimitiveErrorBound R +
              cubicDensityUpperBound R / (Nat.card (ResidueField R) : ℝ) ^ 5 :=
            add_le_add hPu (div_le_div_of_nonneg_right hσu (pow_pos hq _).le)
          _ = cubicDensityUpperBound R := cubicDensityUpperBound_fixed_point
      · intro e he
        have heq : e = (e - 3) + 3 := by omega
        dsimp [σ']
        rw [heq, ha, normalized_cubic_count_scaling_recurrence h3 hπ,
          hE (e - 3) (by omega)]

/-- Uniform bounds on the actual full local density, including nonunit targets. -/
theorem good_prime_cubic_density_bounds
    (h6 : (6 : ResidueField R) ≠ 0) {a : R} (ha : a ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount R 8 e a) atTop (𝓝 σ)) :
    0 ≤ σ ∧ 1 - cubicPrimitiveErrorBound R ≤ σ ∧ σ ≤ cubicDensityUpperBound R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨σ', hσ', E, hE⟩ := good_prime_cubic_unit_pow_bounded_limit h6 hπ u k
  have hlim' : Tendsto (fun e => normalizedLocalCubicCount R 8 e ((u : R) * π ^ k))
      atTop (𝓝 σ') := by
    apply Tendsto.congr' _ tendsto_const_nhds
    exact eventually_atTop.mpr ⟨E, fun e he => (hE e he).symm⟩
  have hσ : σ = σ' := tendsto_nhds_unique hlim hlim'
  exact hσ ▸ hσ'

/-- Target-uniform Euler-factor error at all residue characteristics except
2 and 3. In particular this is a summable `O(q^(-3/2))` tail. -/
theorem good_prime_cubic_density_error_sq
    (h6 : (6 : ResidueField R) ≠ 0) {a : R} (ha : a ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount R 8 e a) atTop (𝓝 σ)) :
    (σ - 1) ^ 2 ≤ 576 / (Nat.card (ResidueField R) : ℝ) ^ 3 := by
  obtain ⟨-, hlo, hhi⟩ := good_prime_cubic_density_bounds h6 ha hlim
  have hU := one_add_primitive_error_le_density_upper (R := R)
  have habs : |σ - 1| ≤ cubicDensityUpperBound R - 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hbound := habs.trans (cubicDensityUpperBound_error_le_sqrt (R := R))
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hbound 2
  have hq : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  simpa only [sq_abs, div_pow, Real.sq_sqrt (pow_pos hq 3).le, show (24 : ℝ) ^ 2 = 576 by norm_num]
    using hsq

end DVR

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem completion_good_prime_cubic_density_error_sq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    {ν : 𝓞 K} (hν0 : ν ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 σ)) :
    (σ - 1) ^ 2 ≤ 576 / (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) ^ 3 := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  have ha0 : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ≠ 0 := by
    intro h
    apply hν0
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  exact good_prime_cubic_density_error_sq h6 ha0 hlim

/-- Simultaneously: actual convergent positive local densities, explicit
all-prime lower bounds, and the target-uniform summable-scale good-prime tail. -/
theorem completion_cubic_density_family_with_euler_tail
    {ν : 𝓞 K} (hν : Eligible 3 ν) (hν0 : ν ≠ 0) :
    ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ, ∀ v,
      (0 < σ v ∧ completionCubicDensityLowerBound v ≤ σ v ∧
        Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 (σ v))) ∧
      ((6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 →
        (σ v - 1) ^ 2 ≤ 576 / (Nat.card (ResidueField (v.adicCompletionIntegers K)) : ℝ) ^ 3) := by
  obtain ⟨σ, hσ⟩ := completion_cubic_density_family_exists hν hν0
  exact ⟨σ, fun v => ⟨hσ v, fun h6 =>
    completion_good_prime_cubic_density_error_sq v h6 hν0 (hσ v).2.2⟩⟩

end WaringSiegel

#print axioms WaringSiegel.primitive_eight_density_bounds

#print axioms WaringSiegel.good_prime_cubic_density_bounds

#print axioms WaringSiegel.good_prime_cubic_density_error_sq

#print axioms WaringSiegel.completion_cubic_density_family_with_euler_tail
