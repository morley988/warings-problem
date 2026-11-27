import WaringSiegel.WSL3TraceIdealDuality
import WaringSiegel.WSL3LocalCharacterReduction

/-! # WSL3: primitive quotient characters and exact conductor ideals -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

def quotientCharacterConductor {R : Type*} [CommRing R]
    (I : Ideal R) (ψ : AddChar (R ⧸ I) ℂ) : Ideal R :=
  addCharIdealConductor (ψ.compAddMonoidHom (Ideal.Quotient.mk I).toAddMonoidHom)

theorem ideal_le_quotientCharacterConductor {R : Type*} [CommRing R]
    (I : Ideal R) (ψ : AddChar (R ⧸ I) ℂ) : I ≤ quotientCharacterConductor I ψ := by
  intro a ha x
  change ψ (Ideal.Quotient.mk I (a*x)) = 1
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right x ha), ψ.map_zero_eq_one]

theorem quotient_character_factors_iff {R : Type*} [CommRing R]
    {I J : Ideal R} (hIJ : I ≤ J) (ψ : AddChar (R ⧸ I) ℂ) :
    (∃ φ : AddChar (R ⧸ J) ℂ,
      φ.compAddMonoidHom (Ideal.Quotient.factor hIJ).toAddMonoidHom = ψ) ↔
        J ≤ quotientCharacterConductor I ψ := by
  constructor
  · rintro ⟨φ, rfl⟩ a ha x
    change φ (Ideal.Quotient.mk J (a*x)) = 1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right x ha), φ.map_zero_eq_one]
  · intro hJ
    let χ : AddChar R ℂ := ψ.compAddMonoidHom (Ideal.Quotient.mk I).toAddMonoidHom
    have hker : J.toAddSubgroup ≤ χ.toAddMonoidHom.ker := by
      intro a ha
      have h := hJ ha (1 : R)
      simpa only [mul_one] using h
    let f : (R ⧸ J) →+ Additive ℂ := QuotientAddGroup.lift J.toAddSubgroup
      χ.toAddMonoidHom hker
    let φ : AddChar (R ⧸ J) ℂ := AddChar.toAddMonoidHomEquiv.symm f
    refine ⟨φ, ?_⟩
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

variable {K : Type*} [Field K] [NumberField K]

theorem quotientCharacterConductor_eq_traceConductor
    (I : Ideal (𝓞 K)) (ψ : AddChar (𝓞 K ⧸ I) ℂ) (γ : K)
    (hγ : ∀ x : 𝓞 K, ψ (Ideal.Quotient.mk I x) =
      traceTorusCharacter x (traceRationalPoint γ)) :
    quotientCharacterConductor I ψ = traceConductor γ := by
  have h : ψ.compAddMonoidHom (Ideal.Quotient.mk I).toAddMonoidHom =
      traceFrequencyAddChar (traceRationalPoint γ) := by
    ext x
    exact hγ x
  rw [quotientCharacterConductor, h, traceFrequencyAddChar_idealConductor]

theorem primePower_conductor_eq_of_not_le_previous
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (C : Ideal (𝓞 K)) (hC : v.asIdeal^(e+1) ≤ C) (hprev : ¬v.asIdeal^e ≤ C) :
    C = v.asIdeal^(e+1) := by
  have hd : C ∣ v.asIdeal^(e+1) := Ideal.dvd_iff_le.mpr hC
  obtain ⟨m, hm, hassoc⟩ := (dvd_prime_pow v.prime (e+1)).mp hd
  have heq : C = v.asIdeal^m := associated_iff_eq.mp hassoc
  have hmne : ¬m ≤ e := by
    intro hme
    apply hprev
    rw [heq]
    exact Ideal.pow_le_pow_right hme
  have hm' : m = e+1 := by omega
  simpa only [hm'] using heq

theorem primePower_character_not_factors_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ)
    (ψ : AddChar (𝓞 K ⧸ v.asIdeal^(e+1)) ℂ) :
    (¬∃ φ : AddChar (𝓞 K ⧸ v.asIdeal^e) ℂ,
      φ.compAddMonoidHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ e))).toAddMonoidHom = ψ) ↔
      quotientCharacterConductor (v.asIdeal^(e+1)) ψ = v.asIdeal^(e+1) := by
  rw [quotient_character_factors_iff]
  constructor
  · intro h
    exact primePower_conductor_eq_of_not_le_previous v e _
      (ideal_le_quotientCharacterConductor _ ψ) h
  · intro hC hprev
    rw [hC] at hprev
    have hd : v.asIdeal^(e+1) ∣ v.asIdeal^e := Ideal.dvd_iff_le.mpr hprev
    have hle := (pow_dvd_pow_iff v.prime.ne_zero v.prime.not_unit).mp hd
    omega

def primitiveConductorCharacters {R : Type*} [CommRing R]
    (I : Ideal R) [Fintype (AddChar (R ⧸ I) ℂ)] : Finset (AddChar (R ⧸ I) ℂ) :=
  Finset.univ.filter (fun ψ => quotientCharacterConductor I ψ = I)

theorem primePower_primitive_characters_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ)
    [Fintype (𝓞 K ⧸ v.asIdeal^e)] [Fintype (𝓞 K ⧸ v.asIdeal^(e+1))] :
    primitiveConductorCharacters (v.asIdeal^(e+1)) =
      Finset.univ \ Finset.univ.image (fun φ : AddChar (𝓞 K ⧸ v.asIdeal^e) ℂ =>
        φ.compAddMonoidHom (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.le_succ e))).toAddMonoidHom) := by
  ext ψ
  simp only [primitiveConductorCharacters, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff, Finset.mem_image]
  exact (primePower_character_not_factors_iff v e ψ).symm

end WaringSiegel
