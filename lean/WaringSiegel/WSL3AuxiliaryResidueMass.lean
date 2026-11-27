import WaringSiegel.WSL3AuxiliaryFiniteMass
import WaringSiegel.WSL3AuxiliaryUnitInflation

/-! # WSL3: actual exact-conductor weighted residue mass at an auxiliary prime -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem residue_restricted_exact_conductor_weighted_mass
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hq : 173 ≤ Ideal.absNorm v.asIdeal) (ν : 𝓞 K) :
    letI := idealResidueFintype v.asIdeal v.ne_bot
    (∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal) ℂ,
      (Ideal.absNorm (quotientCharacterConductor v.asIdeal ψ) : ℝ)^(5/4 : ℝ) *
        ‖finiteRingRestrictedCubicCharacterTerm 0 (Ideal.Quotient.mk v.asIdeal ν) ψ‖) ≤
      (Ideal.absNorm v.asIdeal : ℝ)^2 := by
  letI := idealResidueFintype v.asIdeal v.ne_bot
  let F := 𝓞 K ⧸ v.asIdeal
  letI : Field F := Ideal.Quotient.field v.asIdeal
  have hc : Fintype.card F = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  let a := fun ψ : AddChar F ℂ =>
    ‖finiteRingRestrictedCubicCharacterTerm 0 (Ideal.Quotient.mk v.asIdeal ν) ψ‖
  let w := fun ψ : AddChar F ℂ =>
    (Ideal.absNorm (quotientCharacterConductor v.asIdeal ψ) : ℝ)^(5/4 : ℝ) * a ψ
  have ha : a 1 = (1-1/(Ideal.absNorm v.asIdeal : ℝ))^4 := by
    unfold a
    rw [finite_field_restricted_trivial_coefficient]
    have he : (((1-1/(Fintype.card F : ℝ))^4 : ℝ) : ℂ) =
        (1-1/(Fintype.card F : ℂ))^4 := by push_cast; rfl
    rw [← he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1-1/(Fintype.card F : ℝ))^4), hc]
  have hw1 : w 1 = a 1 := by
    simp only [w, quotientCharacterConductor_one, ← Ideal.one_eq_top,
      map_one, Nat.cast_one, Real.one_rpow, one_mul]
  have hw (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
      w ψ = (Ideal.absNorm v.asIdeal : ℝ)^(5/4 : ℝ) * a ψ := by
    dsimp only [w]
    rw [residue_character_conductor v ψ hψ]
  have hs : (∑ ψ : AddChar F ℂ, w ψ) =
      (1-1/(Ideal.absNorm v.asIdeal : ℝ))^4 +
        (Ideal.absNorm v.asIdeal : ℝ)^(5/4 : ℝ) *
          ∑ ψ ∈ Finset.univ.erase (1 : AddChar F ℂ), a ψ := by
    rw [← Finset.add_sum_erase Finset.univ w (Finset.mem_univ (1 : AddChar F ℂ)), hw1, ha,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ψ hψ
    exact hw ψ (Finset.mem_erase.mp hψ).1
  change (∑ ψ : AddChar F ℂ, w ψ) ≤ _
  rw [hs]
  simpa only [hc] using
    (finite_field_restricted_weighted_mass_le_square (F := F)
      (hc.symm ▸ hq) (Ideal.Quotient.mk v.asIdeal ν))

end WaringSiegel
#print axioms WaringSiegel.residue_restricted_exact_conductor_weighted_mass
