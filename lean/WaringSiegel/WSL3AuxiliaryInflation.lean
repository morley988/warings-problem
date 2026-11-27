import WaringSiegel.WSL3AuxiliaryProductSums

/-! # WSL3: auxiliary complete sums are unchanged on every common multiple -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliaryCubicCharacterContribution_common_multiple
    (c : CubicConductorCharacter K) (p : 𝓞 K) (hp : p ≠ 0) (ν : 𝓞 K)
    (J : Ideal (𝓞 K)) (hJ : J ≠ 0)
    (hJI : J ≤ c.1.1) (hJP : J ≤ Ideal.span ({p} : Set (𝓞 K))) :
    letI := idealResidueFintype J hJ
    auxiliaryCubicCharacterContribution c p hp ν =
      finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hJP)
        (Ideal.Quotient.mk J p) (Ideal.Quotient.mk J ν)
        (c.2.1.compAddMonoidHom (Ideal.Quotient.factor hJI).toAddMonoidHom) := by
  let M := auxiliaryCommonModulus c.1.1 p
  letI := idealResidueFintype M (auxiliaryCommonModulus_ne_zero c.1.1 c.1.2 p hp)
  letI := idealResidueFintype J hJ
  let u : (𝓞 K ⧸ J) →+* (𝓞 K ⧸ M) := Ideal.Quotient.factor (le_inf hJI hJP)
  let f : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ c.1.1) := Ideal.Quotient.factor inf_le_left
  let g : (𝓞 K ⧸ M) →+* (𝓞 K ⧸ Ideal.span ({p} : Set (𝓞 K))) :=
    Ideal.Quotient.factor inf_le_right
  have huf : f.comp u = Ideal.Quotient.factor hJI := Ideal.Quotient.factor_comp _ _
  have hug : g.comp u = Ideal.Quotient.factor hJP := Ideal.Quotient.factor_comp _ _
  have hχ : (c.2.1.compAddMonoidHom f.toAddMonoidHom).compAddMonoidHom u.toAddMonoidHom =
      c.2.1.compAddMonoidHom (Ideal.Quotient.factor hJI).toAddMonoidHom := by
    ext x
    exact congrArg c.2.1 (RingHom.congr_fun huf x)
  have h := finiteMaskedCubicCharacterTerm_inflation u
    (Ideal.Quotient.factor_surjective (le_inf hJI hJP)) g
    (c.2.1.compAddMonoidHom f.toAddMonoidHom)
    (Ideal.Quotient.mk J p) (Ideal.Quotient.mk J ν)
  rw [hug, hχ] at h
  rw [auxiliaryCubicCharacterContribution_common_modulus c p hp ν]
  exact h.symm

end WaringSiegel
#print axioms WaringSiegel.auxiliaryCubicCharacterContribution_common_multiple
