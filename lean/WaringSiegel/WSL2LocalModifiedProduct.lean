import WaringSiegel.WSL2LocalModifiedDensity

/-!
# Uniform positivity after finitely many modified local factors

The ordinary Euler product has a target-independent positive lower bound.
Replacing each of at most m sufficiently large good-prime factors by its
actual restricted four-unit local density loses at most a factor 4^m.
-/

noncomputable section
set_option maxHeartbeats 0
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical

namespace WaringSiegel

/-- A finite replacement of positive factors has the expected product formula
and quantitative lower bound. -/
theorem finite_replacement_product_lower {ι : Type*}
    (σ ρ : ι → ℝ) (S : Finset ι) (hσ : Multipliable σ)
    (hσpos : ∀ i, 0 < σ i) (hσupper : ∀ i ∈ S, σ i ≤ 2)
    (hρlower : ∀ i ∈ S, (1 / 2 : ℝ) ≤ ρ i)
    {c : ℝ} (hc : 0 < c) (hprod : c ≤ ∏' i, σ i) :
    Multipliable (fun i => if i ∈ S then ρ i else σ i) ∧
      c / (4 : ℝ) ^ S.card ≤ ∏' i, if i ∈ S then ρ i else σ i := by
  let u : ι → ℝ := fun i => if i ∈ S then ρ i / σ i else 1
  have hu : Multipliable u := by
    apply multipliable_of_finite_mulSupport
    apply S.finite_toSet.subset
    intro i hi
    by_contra hn
    change i ∉ S at hn
    exact hi (by simp only [u, if_neg hn])
  have heq (i : ι) : (if i ∈ S then ρ i else σ i) = σ i * u i := by
    dsimp [u]
    split_ifs with hi
    · field_simp [(hσpos i).ne']
    · simp
  have huprod : (∏' i, u i) = ∏ i ∈ S, ρ i / σ i := by
    rw [tprod_eq_prod (s := S) (fun i hi => by simp only [u, if_neg hi])]
    exact Finset.prod_congr rfl (fun i hi => by simp only [u, if_pos hi])
  have hratio (i : ι) (hi : i ∈ S) : (1 / 4 : ℝ) ≤ ρ i / σ i := by
    apply (le_div_iff₀ (hσpos i)).mpr
    nlinarith [hσupper i hi, hρlower i hi]
  have hratioProd : (1 / 4 : ℝ) ^ S.card ≤ ∏ i ∈ S, ρ i / σ i := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by norm_num) hratio
  refine ⟨(hσ.mul hu).congr (fun i => (heq i).symm), ?_⟩
  calc
    c / (4 : ℝ) ^ S.card = c * (1 / 4 : ℝ) ^ S.card := by
      rw [one_div_pow, div_eq_mul_inv, one_div]
    _ ≤ (∏' i, σ i) * ∏ i ∈ S, ρ i / σ i :=
      mul_le_mul hprod hratioProd (by positivity) (hc.le.trans hprod)
    _ = (∏' i, σ i) * ∏' i, u i := by rw [huprod]
    _ = ∏' i, σ i * u i := (hσ.tprod_mul hu).symm
    _ = _ := tprod_congr (fun i => (heq i).symm)

variable {K : Type*} [Field K] [NumberField K]

def cubicModifiedResidueFactor
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν : 𝓞 K) : ℝ :=
  (finiteFieldFourUnitCubicCount (ResidueField (v.adicCompletionIntegers K))
    (residue (v.adicCompletionIntegers K)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) : ℝ) /
        (Ideal.absNorm v.asIdeal : ℝ) ^ 3

theorem cubicModifiedResidueFactor_lower
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 24576 ≤ Ideal.absNorm v.asIdeal) (ν : 𝓞 K) :
    (1 / 2 : ℝ) ≤ cubicModifiedResidueFactor v ν := by
  letI := completionIntegers_residueFinite v
  letI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers K))
  have h6' : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    fun h => h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hq' : 24576 ≤ Fintype.card (ResidueField (v.adicCompletionIntegers K)) := by
    simpa only [← Nat.card_eq_fintype_card, completion_residue_card_eq_absNorm] using hq
  simpa only [cubicModifiedResidueFactor, ← Nat.card_eq_fintype_card,
    completion_residue_card_eq_absNorm] using
    finite_field_four_unit_cubic_normalized_lower h6' hq'
      (residue (v.adicCompletionIntegers K) (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν))

theorem ordinary_cubic_factor_le_two_at_large_good_prime
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 24576 ≤ Ideal.absNorm v.asIdeal)
    {ν : 𝓞 K} (hν0 : ν ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 σ)) :
    σ ≤ 2 := by
  have herror := original_good_prime_cubic_density_error_sq v h6 hν0 hlim
  have hqR : (24576 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast hq
  have hqpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hpow : (576 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24576) hqR 3
    norm_num at h
    linarith
  have he1 : (σ - 1) ^ 2 ≤ 1 := herror.trans ((div_le_one (pow_pos hqpos 3)).mpr hpow)
  have ha := abs_le_of_sq_le_sq (by simpa only [one_pow] using he1) (by norm_num : (0 : ℝ) ≤ 1)
  linarith [(abs_le.mp ha).2]

/-- One field-dependent constant survives replacing any finite set of
sufficiently large good-prime factors by their actual modified local factors. -/
theorem modified_cubic_euler_product_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
          atTop (𝓝 (σ v))) ∧
        ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
          (∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal ∧ 24576 ≤ Ideal.absNorm v.asIdeal) →
          Multipliable (fun v => if v ∈ S then cubicModifiedResidueFactor v ν else σ v) ∧
            c / (4 : ℝ) ^ S.card ≤
              ∏' v, if v ∈ S then cubicModifiedResidueFactor v ν else σ v := by
  obtain ⟨c, hc, hordinary⟩ := original_cubic_euler_product_uniform_positive (K := K)
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, _, hmul, hbound⟩ := hordinary ν hν hν0
  refine ⟨σ, fun v => ⟨(hσ v).1, (hσ v).2.2⟩, ?_⟩
  intro S hS
  exact finite_replacement_product_lower σ (fun v => cubicModifiedResidueFactor v ν) S
    hmul (fun v => (hσ v).1)
    (fun v hv => ordinary_cubic_factor_le_two_at_large_good_prime v
      (hS v hv).1 (hS v hv).2 hν0 (hσ v).2.2)
    (fun v hv => cubicModifiedResidueFactor_lower v (hS v hv).1 (hS v hv).2 ν)
    hc hbound

/-- The replacement factor is the genuine higher-precision restricted density. -/
theorem cubicModifiedResidueFactor_eq_normalized_count
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) {p : 𝓞 K} (hp : p ∈ v.asIdeal)
    (ν : 𝓞 K) (n : ℕ) :
    cubicModifiedResidueFactor v ν =
      normalizedModifiedLocalCubicCount (v.adicCompletionIntegers K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) p)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) n := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  have h6' : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    fun h => h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hp' : algebraMap (𝓞 K) (v.adicCompletionIntegers K) p ∈
      maximalIdeal (v.adicCompletionIntegers K) := by
    simpa only [pow_one] using
      (completion_mem_maximalIdeal_pow_iff v p 1).mpr (by simpa only [pow_one] using hp)
  rw [normalized_modified_local_cubic_count_eq
    (three_isUnit_of_six_residue_ne_zero h6') hp', completion_residue_card_eq_absNorm]
  rfl

/-- If at most m primes are modified, one constant works independently of the
chosen finite set and target. -/
theorem modified_cubic_euler_product_uniform_positive_of_card_le (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
          atTop (𝓝 (σ v))) ∧
        ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)), S.card ≤ m →
          (∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal ∧ 24576 ≤ Ideal.absNorm v.asIdeal) →
          Multipliable (fun v => if v ∈ S then cubicModifiedResidueFactor v ν else σ v) ∧
            c ≤ ∏' v, if v ∈ S then cubicModifiedResidueFactor v ν else σ v := by
  obtain ⟨c, hc, hfamily⟩ := modified_cubic_euler_product_uniform_positive (K := K)
  refine ⟨c / (4 : ℝ) ^ m, by positivity, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, hreplace⟩ := hfamily ν hν hν0
  refine ⟨σ, hσ, ?_⟩
  intro S hcard hS
  obtain ⟨hmul, hbound⟩ := hreplace S hS
  refine ⟨hmul, le_trans ?_ hbound⟩
  exact div_le_div_of_nonneg_left hc.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hcard)

end WaringSiegel

#print axioms WaringSiegel.modified_cubic_euler_product_uniform_positive

#print axioms WaringSiegel.modified_cubic_euler_product_uniform_positive_of_card_le
