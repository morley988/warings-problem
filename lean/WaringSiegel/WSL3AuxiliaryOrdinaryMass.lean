import WaringSiegel.WSL3AuxiliaryFiniteIndex

/-! # WSL3: the unrestricted finite factor inherits the actual global ordinary budget -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem finite_ordinary_exact_conductor_mass_le
    (M : Ideal (𝓞 K)) (hM : M ≠ 0) (ν : 𝓞 K) :
    letI := idealResidueFintype M hM
    (∑ ψ : AddChar (𝓞 K ⧸ M) ℂ,
      (Ideal.absNorm (quotientCharacterConductor M ψ) : ℝ)^(5/4 : ℝ) *
        ‖finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk M ν) ψ‖) ≤
      cubicSharpUniformSingularSeriesConstant K := by
  letI := idealResidueFintype M hM
  letI := conductorCharactersUnderFintype M hM
  let w := fun c : CubicConductorCharacter K =>
    (Ideal.absNorm c.1.1 : ℝ)^(5/4 : ℝ) * ‖cubicCharacterContribution c ν‖
  let f := fun ψ : AddChar (𝓞 K ⧸ M) ℂ =>
    (Ideal.absNorm (quotientCharacterConductor M ψ) : ℝ)^(5/4 : ℝ) *
      ‖finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk M ν) ψ‖
  have he (c : ConductorCharactersUnder M) :
      f ((conductorCharactersUnderEquiv M hM) c) = w c.1 := by
    letI := idealResidueFintype c.1.1.1 c.1.1.2
    change (Ideal.absNorm (quotientCharacterConductor M (conductorCharacterInflation M c)) : ℝ)^(5/4 : ℝ) *
      ‖finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk M ν) (conductorCharacterInflation M c)‖ = _
    rw [conductorCharacterInflation_conductor]
    unfold conductorCharacterInflation
    rw [finite_ring_power_character_term_inflation (Ideal.Quotient.factor c.2)
      (Ideal.Quotient.factor_surjective c.2)]
    rfl
  have hsum : (∑ ψ : AddChar (𝓞 K ⧸ M) ℂ, f ψ) =
      ∑ c : ConductorCharactersUnder M, w c.1 := by
    have hs := (conductorCharactersUnderEquiv M hM).bijective.sum_comp f
    simpa only [he] using hs.symm
  obtain ⟨hs,hb⟩ := cubicCharacterContribution_five_quarters_uniform_bound ν
  change Summable w at hs
  change (∑' c, w c) ≤ cubicSharpUniformSingularSeriesConstant K at hb
  have hsub : (∑ c : ConductorCharactersUnder M, w c.1) ≤ ∑' c, w c := by
    have ht : (∑' c : ConductorCharactersUnder M, w c.1) ≤ ∑' c, w c :=
      Summable.tsum_le_tsum_of_inj (fun c : ConductorCharactersUnder M => c.1)
      Subtype.val_injective (fun c _ => by dsimp [w]; positivity)
      (fun _ => le_rfl) Summable.of_finite hs
    simpa only [tsum_fintype] using ht
  change (∑ ψ : AddChar (𝓞 K ⧸ M) ℂ, f ψ) ≤ _
  exact hsum.trans_le (hsub.trans hb)

theorem finiteMaskedConductorMass_unrestricted_le
    (M : Ideal (𝓞 K)) (hM : M ≠ 0) (p ν : 𝓞 K)
    (hp : IsUnit (Ideal.Quotient.mk M p)) :
    letI := idealResidueFintype M hM
    finiteMaskedConductorMass M ⊤ le_top p ν (5/4 : ℝ) ≤
      cubicSharpUniformSingularSeriesConstant K := by
  letI := idealResidueFintype M hM
  unfold finiteMaskedConductorMass
  simp only [finiteMaskedCubicCharacterTerm_unrestricted _ _ _ _ hp]
  exact finite_ordinary_exact_conductor_mass_le M hM ν

end WaringSiegel
#print axioms WaringSiegel.finite_ordinary_exact_conductor_mass_le
#print axioms WaringSiegel.finiteMaskedConductorMass_unrestricted_le
