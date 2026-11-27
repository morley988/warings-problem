import WaringSiegel.WSL3ConductorCRT
import Mathlib.RingTheory.Coprime.Lemmas

/-! # WSL3: actual ideal conductor coefficients and finite Euler factorization -/
noncomputable section
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def idealResidueFintype (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Fintype (𝓞 K ⧸ I) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot I hI
  exact Fintype.ofFinite _

def idealPrimitiveCubicCoefficient (I : Ideal (𝓞 K)) (hI : I ≠ 0) (ν : 𝓞 K) : ℂ :=
  letI := idealResidueFintype I hI
  ∑ ψ ∈ primitiveConductorCharacters I,
    finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk I ν) ψ

@[simp] theorem idealPrimitiveCubicCoefficient_prime_pow
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient (v.asIdeal^e) (pow_ne_zero e v.ne_bot) ν =
      primePowerPrimitiveCubicCoefficient v e ν := by
  rfl

@[simp] theorem idealPrimitiveCubicCoefficient_top (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient ⊤ top_ne_bot ν = 1 := by
  letI := idealResidueFintype (⊤ : Ideal (𝓞 K)) top_ne_bot
  letI : Unique (𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) :=
    { default := 0
      uniq := fun _ => Subsingleton.elim _ _ }
  have hC (ψ : AddChar (𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) ℂ) :
      quotientCharacterConductor ⊤ ψ = ⊤ := by
    apply top_unique
    exact ideal_le_quotientCharacterConductor ⊤ ψ
  simp only [idealPrimitiveCubicCoefficient, primitiveConductorCharacters,
    hC, Finset.filter_true, finiteRingPowerCharacterTerm]
  rw [finite_ring_power_normalized_character_count 3 8 (by decide)]
  change (localCubicSolutionCount (𝓞 K) ⊤ 8 ν : ℂ) /
    (Fintype.card (𝓞 K ⧸ (⊤ : Ideal (𝓞 K))) : ℂ)^(8-1) = 1
  simp only [localCubicSolutionCount_top, Fintype.card_unique, Nat.cast_one, one_pow, div_one]

@[simp] theorem idealPrimitiveCubicCoefficient_one (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient 1 one_ne_zero ν = 1 := by
  simpa only [Ideal.one_eq_top] using idealPrimitiveCubicCoefficient_top ν

theorem idealPrimitiveCubicCoefficient_mul
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0) (h : IsCoprime I J) (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient (I*J) (mul_ne_zero hI hJ) ν =
      idealPrimitiveCubicCoefficient I hI ν * idealPrimitiveCubicCoefficient J hJ ν := by
  letI := idealResidueFintype I hI
  letI := idealResidueFintype J hJ
  letI := idealResidueFintype (I*J) (mul_ne_zero hI hJ)
  exact primitiveConductorCharacterSum_mul I J h 3 8 ν

theorem heightOne_prime_powers_coprime
    (v w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (h : v ≠ w) (a b : ℕ) :
    IsCoprime (v.asIdeal^a) (w.asIdeal^b) := by
  have hvw : v.asIdeal ≠ w.asIdeal := fun h' => h (IsDedekindDomain.HeightOneSpectrum.ext h')
  exact (Ideal.isCoprime_of_isMaximal hvw).pow

theorem prime_power_product_ne_zero
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ) :
    (∏ v ∈ S, v.asIdeal ^ e v) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.ne_bot)

/-- The literal coefficient at a finite product of distinct prime powers
equals the product of the literal local conductor coefficients. -/
theorem idealPrimitiveCubicCoefficient_finset_prod
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℕ) (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient (∏ v ∈ S, v.asIdeal^e v)
      (prime_power_product_ne_zero S e) ν =
      ∏ v ∈ S, primePowerPrimitiveCubicCoefficient v (e v) ν := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using idealPrimitiveCubicCoefficient_one ν
  | @insert v S hv ih =>
    have hcop : IsCoprime (v.asIdeal^e v) (∏ w ∈ S, w.asIdeal^e w) := by
      apply IsCoprime.prod_right
      intro w hw
      exact heightOne_prime_powers_coprime v w (fun he => hv (he ▸ hw)) _ _
    simp only [Finset.prod_insert hv]
    rw [idealPrimitiveCubicCoefficient_mul _ _ (pow_ne_zero _ v.ne_bot)
      (prime_power_product_ne_zero S e) hcop,
      idealPrimitiveCubicCoefficient_prime_pow, ih]

end WaringSiegel

#print axioms WaringSiegel.idealPrimitiveCubicCoefficient_finset_prod
