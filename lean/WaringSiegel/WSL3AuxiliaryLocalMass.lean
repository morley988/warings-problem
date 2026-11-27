import WaringSiegel.WSL3AuxiliaryResidueMass
import WaringSiegel.WSL3AuxiliaryLocalVanishing

/-! # WSL3: uniform exact-conductor mass at every auxiliary prime-power modulus -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem prime_power_restricted_weighted_mass_eq_residue
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (n : ℕ) (p ν : 𝓞 K) (hpv : p ∈ v.asIdeal)
    (t : ℝ) :
    letI := idealResidueFintype (v.asIdeal^(n+1)) (pow_ne_zero _ v.ne_bot)
    letI := idealResidueFintype v.asIdeal v.ne_bot
    (∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal^(n+1)) ℂ,
      (Ideal.absNorm (quotientCharacterConductor (v.asIdeal^(n+1)) ψ) : ℝ)^t *
        ‖finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.mk (v.asIdeal^(n+1)) p)
          (Ideal.Quotient.mk (v.asIdeal^(n+1)) ν) ψ‖) =
      ∑ φ : AddChar (𝓞 K ⧸ v.asIdeal) ℂ,
        (Ideal.absNorm (quotientCharacterConductor v.asIdeal φ) : ℝ)^t *
          ‖finiteRingRestrictedCubicCharacterTerm 0 (Ideal.Quotient.mk v.asIdeal ν) φ‖ := by
  let M := v.asIdeal^(n+1)
  letI := idealResidueFintype M (pow_ne_zero _ v.ne_bot)
  letI := idealResidueFintype v.asIdeal v.ne_bot
  have hMv : M ≤ v.asIdeal := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let f := fun φ : AddChar (𝓞 K ⧸ v.asIdeal) ℂ =>
    φ.compAddMonoidHom (Ideal.Quotient.factor hMv).toAddMonoidHom
  let g := fun ψ : AddChar (𝓞 K ⧸ M) ℂ =>
    (Ideal.absNorm (quotientCharacterConductor M ψ) : ℝ)^t *
      ‖finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.mk M p)
        (Ideal.Quotient.mk M ν) ψ‖
  let T : Finset (AddChar (𝓞 K ⧸ M) ℂ) := Finset.univ.image f
  have hz (ψ : AddChar (𝓞 K ⧸ M) ℂ) (hψ : ψ ∉ T) : g ψ = 0 := by
    have hC : ¬v.asIdeal ≤ quotientCharacterConductor M ψ := by
      intro hC
      obtain ⟨φ,hφ⟩ := (quotient_character_factors_iff hMv ψ).mpr hC
      exact hψ (Finset.mem_image.mpr ⟨φ,Finset.mem_univ _,hφ⟩)
    unfold g
    rw [original_restricted_cubic_term_vanishes_of_not_le_residue v h6 n ψ hC p ν,
      norm_zero, mul_zero]
  have hf (φ : AddChar (𝓞 K ⧸ v.asIdeal) ℂ) :
      g (f φ) = (Ideal.absNorm (quotientCharacterConductor v.asIdeal φ) : ℝ)^t *
        ‖finiteRingRestrictedCubicCharacterTerm 0 (Ideal.Quotient.mk v.asIdeal ν) φ‖ := by
    unfold g f
    rw [quotientCharacterConductor_inflation,
      finite_restricted_cubic_character_inflation M v.asIdeal hMv (n+1) le_rfl,
      Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpv]
  change (∑ ψ : AddChar (𝓞 K ⧸ M) ℂ, g ψ) = _
  calc
    _ = ∑ ψ ∈ T, g ψ :=
      (Finset.sum_subset (Finset.subset_univ T) (fun ψ _ hψ => hz ψ hψ)).symm
    _ = ∑ φ : AddChar (𝓞 K ⧸ v.asIdeal) ℂ, g (f φ) := by
      exact Finset.sum_image (fun _ _ _ _ he => quotient_character_inflation_injective hMv he)
    _ = _ := by simp only [hf]

/-- No conductor level is omitted: every character of the original prime
power quotient is included, with its exact conductor norm. -/
theorem prime_power_restricted_weighted_mass_le_square
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 173 ≤ Ideal.absNorm v.asIdeal)
    (n : ℕ) (p ν : 𝓞 K) (hpv : p ∈ v.asIdeal) :
    letI := idealResidueFintype (v.asIdeal^(n+1)) (pow_ne_zero _ v.ne_bot)
    (∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal^(n+1)) ℂ,
      (Ideal.absNorm (quotientCharacterConductor (v.asIdeal^(n+1)) ψ) : ℝ)^(5/4 : ℝ) *
        ‖finiteRingRestrictedCubicCharacterTerm (Ideal.Quotient.mk (v.asIdeal^(n+1)) p)
          (Ideal.Quotient.mk (v.asIdeal^(n+1)) ν) ψ‖) ≤
      (Ideal.absNorm v.asIdeal : ℝ)^2 := by
  letI := idealResidueFintype (v.asIdeal^(n+1)) (pow_ne_zero _ v.ne_bot)
  letI := idealResidueFintype v.asIdeal v.ne_bot
  rw [prime_power_restricted_weighted_mass_eq_residue v h6 n p ν hpv]
  exact residue_restricted_exact_conductor_weighted_mass v hq ν

/-- The same bound holds for a unit mask at any positive power of this prime,
including ramified auxiliary moduli. -/
theorem prime_power_masked_weighted_mass_le_square
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 173 ≤ Ideal.absNorm v.asIdeal)
    (n e : ℕ) (he : 1 ≤ e) (hen : e ≤ n+1) (p ν : 𝓞 K) (hpv : p ∈ v.asIdeal) :
    letI := idealResidueFintype (v.asIdeal^(n+1)) (pow_ne_zero _ v.ne_bot)
    finiteMaskedConductorMass (v.asIdeal^(n+1)) (v.asIdeal^e)
      (Ideal.pow_le_pow_right hen) p ν (5/4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ)^2 := by
  letI := idealResidueFintype (v.asIdeal^(n+1)) (pow_ne_zero _ v.ne_bot)
  have hpowers : (v.asIdeal^e)^(n+1) ≤ v.asIdeal^(n+1) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by nlinarith : n+1 ≤ e*(n+1))
  unfold finiteMaskedConductorMass
  simp only [finiteMaskedCubicCharacterTerm_factor_of_power_le
    (v.asIdeal^(n+1)) (v.asIdeal^e) (Ideal.pow_le_pow_right hen) (n+1) hpowers]
  exact prime_power_restricted_weighted_mass_le_square v h6 hq n p ν hpv

end WaringSiegel
#print axioms WaringSiegel.prime_power_restricted_weighted_mass_eq_residue
#print axioms WaringSiegel.prime_power_masked_weighted_mass_le_square
