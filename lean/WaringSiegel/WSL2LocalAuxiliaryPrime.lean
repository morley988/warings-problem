import WaringSiegel.WSL2LocalModifiedProduct

/-!
# Uniform modified Euler products at auxiliary rational primes

The rational prime p injects its prime field into every residue field above
p, so N𝔭≥p. Distinct prime ideals above p have a product dividing (p);
absolute norms therefore bound their number by [K:Q]. These facts close the
uniform auxiliary-prime modified-product positivity statement.
-/

noncomputable section
set_option maxHeartbeats 0
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem rational_prime_le_residue_norm
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hp : p.Prime) (hpv : (p : 𝓞 K) ∈ v.asIdeal) :
    p ≤ Ideal.absNorm v.asIdeal := by
  let F := ResidueField (v.adicCompletionIntegers K)
  letI := completionIntegers_residueFinite v
  letI := Fintype.ofFinite F
  have hp0 : (p : F) = 0 := (completion_residue_natCast_eq_zero_iff v p).mpr hpv
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  have hdiv : p ∣ Fintype.card F :=
    (CharP.cast_eq_zero_iff F p _).mp (FiniteField.cast_card_eq_zero F)
  have hle := Nat.le_of_dvd (Fintype.card_pos (α := F)) hdiv
  simpa only [F, ← Nat.card_eq_fintype_card, completion_residue_card_eq_absNorm] using hle

theorem prime_above_large_rational_prime_avoids_six
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hp : p.Prime) (hp6 : 6 < p) (hpv : (p : 𝓞 K) ∈ v.asIdeal) :
    (6 : 𝓞 K) ∉ v.asIdeal := by
  let F := ResidueField (v.adicCompletionIntegers K)
  have hp0 : (p : F) = 0 := (completion_residue_natCast_eq_zero_iff v p).mpr hpv
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0
  intro h6
  have h60 : (6 : F) = 0 := (completion_residue_natCast_eq_zero_iff v 6).mpr h6
  have hd : p ∣ 6 := (CharP.cast_eq_zero_iff F p 6).mp h60
  exact (Nat.not_le_of_lt hp6) (Nat.le_of_dvd (by decide : 0 < 6) hd)

theorem prime_ideals_above_rational_prime_card_le
    {p : ℕ} (hp : p.Prime)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∈ S, (p : 𝓞 K) ∈ v.asIdeal) :
    S.card ≤ Module.finrank ℚ K := by
  have hdiv : (∏ v ∈ S, v.asIdeal) ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
    apply Finset.prod_dvd_of_coprime
    · intro v hv w hw hne
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      exact hne (IsDedekindDomain.HeightOneSpectrum.ext heq)
    · intro v hv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hS v hv
  have hnorm := map_dvd Ideal.absNorm hdiv
  rw [map_prod, ideal_absNorm_span_nat] at hnorm
  have hu : (∏ v ∈ S, Ideal.absNorm v.asIdeal) ≤ p ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (pow_pos hp.pos _) hnorm
  have hl : p ^ S.card ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun v hv => rational_prime_le_residue_norm v hp (hS v hv))
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hl.trans hu)

theorem prime_ideals_containing_nat_finite {p : ℕ} (hp : p ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hspan : Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ≠ 0 := by
    apply mt Ideal.span_singleton_eq_bot.mp
    exact_mod_cast hp
  have hf := (IdealDivisorBounds.idealDivisors_finite _ hspan).preimage
    (f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v _ w _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
  apply hf.subset
  intro v hv
  change v.asIdeal ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def cubicAuxiliaryPrimeSet (p : ℕ) (hp : p.Prime) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (prime_ideals_containing_nat_finite (K := K) hp.ne_zero).toFinset

@[simp] theorem mem_cubicAuxiliaryPrimeSet {p : ℕ} (hp : p.Prime)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    v ∈ cubicAuxiliaryPrimeSet (K := K) p hp ↔ (p : 𝓞 K) ∈ v.asIdeal :=
  (prime_ideals_containing_nat_finite (K := K) hp.ne_zero).mem_toFinset

/-- The modified product has one positive lower bound for all eligible
nonzero targets and all rational auxiliary primes p≥24576. -/
theorem auxiliary_prime_modified_cubic_euler_product_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
          atTop (𝓝 (σ v))) ∧
        ∀ (p : ℕ) (hp : p.Prime), 24576 ≤ p →
          Multipliable (fun v => if v ∈ cubicAuxiliaryPrimeSet (K := K) p hp
            then cubicModifiedResidueFactor v ν else σ v) ∧
            c ≤ ∏' v, if v ∈ cubicAuxiliaryPrimeSet (K := K) p hp
              then cubicModifiedResidueFactor v ν else σ v := by
  obtain ⟨c, hc, hfamily⟩ :=
    modified_cubic_euler_product_uniform_positive_of_card_le (K := K) (Module.finrank ℚ K)
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, hreplace⟩ := hfamily ν hν hν0
  refine ⟨σ, hσ, ?_⟩
  intro p hp hlarge
  apply hreplace (cubicAuxiliaryPrimeSet (K := K) p hp)
  · exact prime_ideals_above_rational_prime_card_le hp _
      (fun v hv => (mem_cubicAuxiliaryPrimeSet hp v).mp hv)
  · intro v hv
    have hpv := (mem_cubicAuxiliaryPrimeSet hp v).mp hv
    exact ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hpv,
      hlarge.trans (rational_prime_le_residue_norm v hp hpv)⟩

end WaringSiegel

#print axioms WaringSiegel.prime_ideals_above_rational_prime_card_le
#print axioms WaringSiegel.auxiliary_prime_modified_cubic_euler_product_uniform_positive
