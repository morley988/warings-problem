import WaringSiegel.WSL3AuxiliaryMaskCRT

/-! # WSL3: exact weighted character-mass factorization for masked complete sums -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem quotientCharacterConductor_inflation
    {R : Type*} [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
    (ψ : AddChar (R ⧸ J) ℂ) :
    quotientCharacterConductor I
      (ψ.compAddMonoidHom (Ideal.Quotient.factor hIJ).toAddMonoidHom) =
      quotientCharacterConductor J ψ := by
  ext a
  rfl

@[simp] theorem quotientCharacterConductor_one
    {R : Type*} [CommRing R] (I : Ideal R) :
    quotientCharacterConductor I (1 : AddChar (R ⧸ I) ℂ) = ⊤ := by
  ext a
  simp [quotientCharacterConductor, addCharIdealConductor]

theorem quotientCharacterConductor_eq_top_iff
    {R : Type*} [CommRing R] (I : Ideal R) (ψ : AddChar (R ⧸ I) ℂ) :
    quotientCharacterConductor I ψ = ⊤ ↔ ψ = 1 := by
  constructor
  · intro h
    ext x
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : (1 : R) ∈ quotientCharacterConductor I ψ := by rw [h]; trivial
    have hh := h1 a
    simpa only [one_mul, AddChar.one_apply] using hh
  · intro h
    rw [h, quotientCharacterConductor_one]

variable {K : Type*} [Field K] [NumberField K]

theorem residue_character_conductor
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (𝓞 K ⧸ v.asIdeal) ℂ) (hψ : ψ ≠ 1) :
    quotientCharacterConductor v.asIdeal ψ = v.asIdeal := by
  exact ((inferInstance : v.asIdeal.IsMaximal).eq_of_le
    (fun h => hψ ((quotientCharacterConductor_eq_top_iff v.asIdeal ψ).mp h))
    (ideal_le_quotientCharacterConductor v.asIdeal ψ)).symm

theorem quotientCharacterConductor_crt_absNorm
    (I J : Ideal (𝓞 K)) (h : IsCoprime I J)
    (ψ : AddChar (𝓞 K ⧸ I) ℂ) (φ : AddChar (𝓞 K ⧸ J) ℂ) :
    Ideal.absNorm (quotientCharacterConductor (I*J) (crtAddCharEquiv I J h (ψ,φ))) =
      Ideal.absNorm (quotientCharacterConductor I ψ) *
        Ideal.absNorm (quotientCharacterConductor J φ) := by
  have hC : IsCoprime (quotientCharacterConductor I ψ) (quotientCharacterConductor J φ) := by
    obtain ⟨i,hi,j,hj,hij⟩ := h.exists
    exact Ideal.isCoprime_iff_exists.mpr
      ⟨i,ideal_le_quotientCharacterConductor I ψ hi,
       j,ideal_le_quotientCharacterConductor J φ hj,hij⟩
  rw [quotientCharacterConductor_crt, Ideal.inf_eq_mul_of_isCoprime hC, map_mul]

/-- Weighted absolute mass over every actual character of the finite quotient.
The weight uses its exact ideal conductor, even when the ambient modulus is larger. -/
def finiteMaskedConductorMass (I A : Ideal (𝓞 K)) (hIA : I ≤ A)
    [Fintype (𝓞 K ⧸ I)] (p ν : 𝓞 K) (t : ℝ) : ℝ :=
  ∑ ψ : AddChar (𝓞 K ⧸ I) ℂ,
    (Ideal.absNorm (quotientCharacterConductor I ψ) : ℝ)^t *
      ‖finiteMaskedCubicCharacterTerm (Ideal.Quotient.factor hIA)
        (Ideal.Quotient.mk I p) (Ideal.Quotient.mk I ν) ψ‖

theorem finiteMaskedConductorMass_crt
    (I J A B : Ideal (𝓞 K)) (h : IsCoprime I J) (hIA : I ≤ A) (hJB : J ≤ B)
    [Fintype (𝓞 K ⧸ I)] [Fintype (𝓞 K ⧸ J)] [Fintype (𝓞 K ⧸ I*J)]
    (p ν : 𝓞 K) (t : ℝ) :
    finiteMaskedConductorMass (I*J) (A*B) (mul_le_mul' hIA hJB) p ν t =
      finiteMaskedConductorMass I A hIA p ν t * finiteMaskedConductorMass J B hJB p ν t := by
  unfold finiteMaskedConductorMass
  rw [← (crtAddCharEquiv I J h).bijective.sum_comp]
  simp only [quotientCharacterConductor_crt_absNorm, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  apply Finset.sum_congr rfl
  intro φ _
  rw [finiteMaskedCubicCharacterTerm_crt I J A B h hIA hJB ψ φ p ν, norm_mul]
  ring

end WaringSiegel
#print axioms WaringSiegel.finiteMaskedConductorMass_crt
#print axioms WaringSiegel.quotientCharacterConductor_inflation
