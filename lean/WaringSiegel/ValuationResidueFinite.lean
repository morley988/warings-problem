import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Finite residue fields of the original finite-place valuation rings

The valuation ring in the fraction field is the localization at the corresponding
prime. We prove this via a local homomorphism from that localization and the
valuation-ring alternative x or x⁻¹. Finite residue then follows from the actual
finite quotient of the ring of integers by the prime ideal.
-/

noncomputable section
open scoped NumberField
namespace WaringSiegel

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private def toValuationIntegers (v : IsDedekindDomain.HeightOneSpectrum R) :
    R →+* (v.valuation K).integer :=
  (algebraMap R K).codRestrict _ (fun r => v.valuation_le_one r)

private theorem toValuationIntegers_unit_iff
    (v : IsDedekindDomain.HeightOneSpectrum R) (r : R) :
    IsUnit (toValuationIntegers (K := K) v r) ↔ r ∉ v.asIdeal := by
  rw [← not_iff_not]
  simp only [not_not, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change v.valuation K (algebraMap R K r) < 1 ↔ r ∈ v.asIdeal
  rw [v.valuation_of_algebraMap]
  exact v.intValuation_lt_one_iff_mem r

/-- The residue of the v-valuation ring is finite whenever R/v is finite. -/
theorem finite_valuationResidue_of_finite_quotient
    (v : IsDedekindDomain.HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.valuation K).integer) := by
  let A := Localization.AtPrime v.asIdeal
  let B := (v.valuation K).integer
  let g : R →+* B := toValuationIntegers v
  have hg (s : v.asIdeal.primeCompl) : IsUnit (g s) :=
    (toValuationIntegers_unit_iff (K := K) v s).mpr s.property
  let f : A →+* B := IsLocalization.lift hg
  have hf_apply (r : R) : f (algebraMap R A r) = g r :=
    IsLocalization.lift_eq hg r
  haveI : IsLocalHom f := ⟨by
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl x
    apply (IsLocalization.AtPrime.isUnit_mk'_iff A v.asIdeal a s).mpr
    apply (toValuationIntegers_unit_iff (K := K) v a).mp
    change IsUnit (g a)
    rw [← hf_apply, ← IsLocalization.mk'_spec A a s, map_mul]
    exact hx.mul (by rw [hf_apply]; exact hg s)⟩
  let j : A →+* K := B.subtype.comp f
  letI : Algebra A K := j.toAlgebra
  haveI : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R K r = (f (algebraMap R A r) : K)
    rw [hf_apply]
    rfl
  haveI : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl A K
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot A
  have hf_surj : Function.Surjective f := by
    intro b
    by_cases hb : b = 0
    · exact ⟨0, by simp [hb]⟩
    have hbK : (b : K) ≠ 0 := fun h => hb (Subtype.ext h)
    rcases ValuationRing.isInteger_or_isInteger A (b : K) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, Subtype.ext ha⟩
    · have hfa : IsUnit (f a) := by
        apply isUnit_of_mul_eq_one (f a) b
        apply Subtype.ext
        change j a * (b : K) = 1
        rw [show j a = (b : K)⁻¹ from ha]
        exact inv_mul_cancel₀ hbK
      have hau : IsUnit a := (isUnit_map_iff f a).mp hfa
      refine ⟨↑(hau.unit⁻¹), ?_⟩
      apply Subtype.ext
      change j ↑(hau.unit⁻¹) = (b : K)
      rw [map_units_inv, hau.unit_spec]
      change (j a)⁻¹ = (b : K)
      rw [show j a = (b : K)⁻¹ from ha, inv_inv]
  haveI : Finite (IsLocalRing.ResidueField A) :=
    Finite.of_surjective (algebraMap (R ⧸ v.asIdeal) v.asIdeal.ResidueField)
      v.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  apply Finite.of_surjective (IsLocalRing.ResidueField.map f)
  intro z
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, rfl⟩ := hf_surj b
  exact ⟨IsLocalRing.residue A a, IsLocalRing.ResidueField.map_residue f a⟩

/-- Original finite-place valuation rings of number fields have finite residue. -/
theorem valuationIntegers_residueFinite {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (v.valuation K).integer) := by
  letI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  exact finite_valuationResidue_of_finite_quotient v

end WaringSiegel

#print axioms WaringSiegel.valuationIntegers_residueFinite
