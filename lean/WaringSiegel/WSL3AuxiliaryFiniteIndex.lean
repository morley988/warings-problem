import WaringSiegel.WSL3AuxiliaryFiniteMass
import WaringSiegel.WSL3AuxiliaryInflation

/-! # WSL3: actual conductor characters below a finite common modulus -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def ConductorCharactersUnder (M : Ideal (𝓞 K)) :=
  {c : CubicConductorCharacter K // M ≤ c.1.1}

def conductorCharacterInflation (M : Ideal (𝓞 K)) (c : ConductorCharactersUnder M) :
    AddChar (𝓞 K ⧸ M) ℂ :=
  c.1.2.1.compAddMonoidHom (Ideal.Quotient.factor c.2).toAddMonoidHom

theorem conductorCharacterInflation_conductor (M : Ideal (𝓞 K))
    (c : ConductorCharactersUnder M) :
    quotientCharacterConductor M (conductorCharacterInflation M c) = c.1.1.1 := by
  rw [conductorCharacterInflation, quotientCharacterConductor_inflation]
  exact c.1.2.2

theorem conductorCharacterInflation_injective (M : Ideal (𝓞 K)) :
    Function.Injective (conductorCharacterInflation M) := by
  rintro ⟨⟨I,ψ⟩,hMI⟩ ⟨⟨J,φ⟩,hMJ⟩ h
  have hIJ : I = J := Subtype.ext (by
    have he := congrArg (quotientCharacterConductor M) h
    simpa only [conductorCharacterInflation_conductor] using he)
  subst J
  have hψ : ψ = φ := Subtype.ext (quotient_character_inflation_injective hMI h)
  subst φ
  rfl

theorem conductorCharacterInflation_surjective (M : Ideal (𝓞 K)) (hM : M ≠ 0) :
    Function.Surjective (conductorCharacterInflation M) := by
  intro ψ
  let C := quotientCharacterConductor M ψ
  have hMC : M ≤ C := ideal_le_quotientCharacterConductor M ψ
  have hC : C ≠ 0 := by
    intro hz
    apply hM
    apply bot_unique
    simpa only [hz] using hMC
  obtain ⟨φ,hφ⟩ := (quotient_character_factors_iff hMC ψ).mpr le_rfl
  have hφC : quotientCharacterConductor C φ = C := by
    rw [← quotientCharacterConductor_inflation M C hMC φ, hφ]
  refine ⟨⟨⟨⟨C,hC⟩,⟨φ,hφC⟩⟩,hMC⟩,?_⟩
  exact hφ

def conductorCharactersUnderEquiv (M : Ideal (𝓞 K)) (hM : M ≠ 0) :
    ConductorCharactersUnder M ≃ AddChar (𝓞 K ⧸ M) ℂ :=
  Equiv.ofBijective (conductorCharacterInflation M)
    ⟨conductorCharacterInflation_injective M, conductorCharacterInflation_surjective M hM⟩

def conductorCharactersUnderFintype (M : Ideal (𝓞 K)) (hM : M ≠ 0) :
    Fintype (ConductorCharactersUnder M) := by
  letI := idealResidueFintype M hM
  exact Fintype.ofEquiv (AddChar (𝓞 K ⧸ M) ℂ) (conductorCharactersUnderEquiv M hM).symm

/-- The finite sum uses the global contribution on the left and the literal
masked quotient sum on the right; exact conductor weights agree under the bijection. -/
theorem auxiliaryCubicCharacterContribution_finite_mass
    (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K) (M : Ideal (𝓞 K)) (hM : M ≠ 0)
    (hMP : M ≤ Ideal.span ({p} : Set (𝓞 K))) (t : ℝ) :
    letI := idealResidueFintype M hM
    letI := conductorCharactersUnderFintype M hM
    (∑ c : ConductorCharactersUnder M,
      (Ideal.absNorm c.1.1.1 : ℝ)^t * ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖) =
      finiteMaskedConductorMass M (Ideal.span ({p} : Set (𝓞 K))) hMP p ν t := by
  letI := idealResidueFintype M hM
  letI := conductorCharactersUnderFintype M hM
  let f := fun ψ : AddChar (𝓞 K ⧸ M) ℂ =>
    (Ideal.absNorm (quotientCharacterConductor M ψ) : ℝ)^t *
      ‖finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hMP)
        (Ideal.Quotient.mk M p) (Ideal.Quotient.mk M ν) ψ‖
  have he (c : ConductorCharactersUnder M) :
      f ((conductorCharactersUnderEquiv M hM) c) =
      (Ideal.absNorm c.1.1.1 : ℝ)^t * ‖auxiliaryCubicCharacterContribution c.1 p hp ν‖ := by
    change (Ideal.absNorm (quotientCharacterConductor M (conductorCharacterInflation M c)) : ℝ)^t *
      ‖finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hMP)
        (Ideal.Quotient.mk M p) (Ideal.Quotient.mk M ν) (conductorCharacterInflation M c)‖ = _
    rw [conductorCharacterInflation_conductor,
      auxiliaryCubicCharacterContribution_common_multiple c.1 p hp ν M hM c.2 hMP]
    rfl
  have hs := (conductorCharactersUnderEquiv M hM).bijective.sum_comp f
  simpa only [he, f, finiteMaskedConductorMass] using hs

end WaringSiegel
#print axioms WaringSiegel.conductorCharactersUnderEquiv
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_finite_mass
