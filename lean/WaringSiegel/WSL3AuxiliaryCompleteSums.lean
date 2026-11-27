import WaringSiegel.WSL3CubicRationalSeries
import WaringSiegel.WSL3RestrictedAbsoluteCharacters

/-! # WSL3: literal auxiliary complete sums on their actual common modulus -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical ComplexConjugate NumberField
namespace WaringSiegel

/-- The restriction is imposed in the specified quotient S. It does not
impose extra unit conditions at primes of R outside that quotient. -/
def finiteMaskedPowerSum {R S : Type*} [CommRing R] [CommRing S] [Fintype R]
    (f : R →+* S) (ψ : AddChar R ℂ) (k : ℕ) : ℂ :=
  ∑ x : R, if IsUnit (f x) then ψ (x^k) else 0

theorem finite_masked_power_average_inflation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Fintype R] [Fintype S]
    (f : R →+* S) (hf : Function.Surjective f) (g : S →+* T)
    (ψ : AddChar S ℂ) (k : ℕ) :
    finiteMaskedPowerSum (g.comp f) (ψ.compAddMonoidHom f.toAddMonoidHom) k /
        (Fintype.card R : ℂ) =
      finiteMaskedPowerSum g ψ k / (Fintype.card S : ℂ) := by
  change (∑ x : R, if IsUnit (g (f x)) then ψ (f (x^k)) else 0) /
      (Fintype.card R : ℂ) =
    (∑ y : S, if IsUnit (g y) then ψ (y^k) else 0) / (Fintype.card S : ℂ)
  simp only [f.map_pow]
  exact finite_average_surjective_addHom f.toAddMonoidHom hf
    (fun x : S => if IsUnit (g x) then ψ (x^k) else 0)


theorem finiteMaskedCubicSum_conj
    {R S : Type*} [CommRing R] [CommRing S] [Fintype R]
    (f : R →+* S) (ψ : AddChar R ℂ) :
    conj (finiteMaskedPowerSum f ψ 3) = finiteMaskedPowerSum f ψ 3 := by
  have ht (x : R) : conj (if IsUnit (f x) then ψ (x^3) else 0) =
      (if IsUnit (f (-x)) then ψ ((-x)^3) else 0) := by
    simp only [map_neg, IsUnit.neg_iff]
    split_ifs
    · rw [← AddChar.inv_apply_eq_conj, ← ψ.map_neg_eq_inv]
      congr 1
      ring
    · exact map_zero _
  simp only [finiteMaskedPowerSum, map_sum, ht]
  exact (Equiv.neg R).bijective.sum_comp
    (fun x : R => if IsUnit (f x) then ψ (x^3) else 0)

variable {K : Type*} [Field K] [NumberField K]

def auxiliaryCommonModulus (I : Ideal (𝓞 K)) (p : 𝓞 K) : Ideal (𝓞 K) :=
  I ⊓ Ideal.span ({p} : Set (𝓞 K))

theorem auxiliaryCommonModulus_ne_zero (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (p : 𝓞 K) (hp : p ≠ 0) : auxiliaryCommonModulus I p ≠ 0 := by
  have hP : Ideal.span ({p} : Set (𝓞 K)) ≠ 0 := mt Ideal.span_singleton_eq_bot.mp hp
  intro h
  have hm : I * Ideal.span ({p} : Set (𝓞 K)) ≤ 0 := by
    have hh : I * Ideal.span ({p} : Set (𝓞 K)) ≤ auxiliaryCommonModulus I p := Ideal.mul_le_inf
    simpa only [h] using hh
  exact mul_ne_zero hI hP (bot_unique hm)

def auxiliaryMaskedCubicAverage (c : CubicConductorCharacter K) (p : 𝓞 K) (hp : p ≠ 0) : ℂ :=
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ c.1.1) := Ideal.Quotient.factor inf_le_left
  let g : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ Ideal.span ({p} : Set (𝓞 K))) := Ideal.Quotient.factor inf_le_right
  finiteMaskedPowerSum g (c.2.1.compAddMonoidHom f.toAddMonoidHom) 3 / (Fintype.card (𝓞 K ⧸ M) : ℂ)

def auxiliaryScaledCubicAverage (c : CubicConductorCharacter K) (p : 𝓞 K) : ℂ :=
  letI := idealResidueFintype c.1.1 c.1.2
  finiteRingScaledPowerSum c.2.1 3 (Ideal.Quotient.mk c.1.1 p) / (Fintype.card (𝓞 K ⧸ c.1.1) : ℂ)

/-- The literal four-unit/four-scaled complete-sum term attached to an exact
conductor character. Unit conditions occur only modulo the auxiliary p. -/
def auxiliaryCubicCharacterContribution (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) : ℂ :=
  auxiliaryMaskedCubicAverage c p hp ^ 4 * auxiliaryScaledCubicAverage c p ^ 4 *
    c.2.1 (-Ideal.Quotient.mk c.1.1 ν)

theorem auxiliaryMaskedCubicAverage_conj (c : CubicConductorCharacter K)
    (p : 𝓞 K) (hp : p ≠ 0) :
    conj (auxiliaryMaskedCubicAverage c p hp) = auxiliaryMaskedCubicAverage c p hp := by
  unfold auxiliaryMaskedCubicAverage
  simp only [map_div₀, finiteMaskedCubicSum_conj, map_natCast]

theorem auxiliaryScaledCubicAverage_conj (c : CubicConductorCharacter K) (p : 𝓞 K) :
    conj (auxiliaryScaledCubicAverage c p) = auxiliaryScaledCubicAverage c p := by
  unfold auxiliaryScaledCubicAverage
  simp only [map_div₀, finiteRingScaledCubicSum_conj, map_natCast]

theorem auxiliaryCubicCharacterContribution_zero_eq_norm
    (c : CubicConductorCharacter K) (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) :
    auxiliaryCubicCharacterContribution c p hp 0 =
      (‖auxiliaryCubicCharacterContribution c p hp ν‖ : ℂ) := by
  letI := idealResidueFintype c.1.1 c.1.2
  have hu : auxiliaryMaskedCubicAverage c p hp ^ 4 =
      ((‖auxiliaryMaskedCubicAverage c p hp‖^4 : ℝ) : ℂ) :=
    complex_even_pow_eq_norm_of_conj_eq (auxiliaryMaskedCubicAverage_conj c p hp) 2
  have hg : auxiliaryScaledCubicAverage c p ^ 4 =
      ((‖auxiliaryScaledCubicAverage c p‖^4 : ℝ) : ℂ) :=
    complex_even_pow_eq_norm_of_conj_eq (auxiliaryScaledCubicAverage_conj c p) 2
  simp only [auxiliaryCubicCharacterContribution, map_zero, neg_zero,
    c.2.1.map_zero_eq_one, mul_one, norm_mul, norm_pow, c.2.1.norm_apply, Complex.ofReal_mul]
  exact congrArg₂ (fun a b : ℂ => a*b) hu hg

end WaringSiegel
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_zero_eq_norm
