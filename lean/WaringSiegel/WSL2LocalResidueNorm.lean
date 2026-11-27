import WaringSiegel.ValuationResidueFinite
import WaringSiegel.DenseValuationResidue
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Completed residue cardinality equals the original prime norm

The original valuation integer ring is isomorphic to localization at the
prime. The dense valuation-preserving embedding into its completion induces
an isomorphism of residue fields. This identifies the literal local `q`
used in the density theorems with the absolute norm of the original prime.
-/

noncomputable section

open IsLocalRing
open scoped NumberField WithZero

namespace WaringSiegel

section Localization

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private def normToValuationIntegers (v : IsDedekindDomain.HeightOneSpectrum R) :
    R →+* (v.valuation K).integer :=
  (algebraMap R K).codRestrict _ (fun r => v.valuation_le_one r)

private theorem normToValuationIntegers_unit_iff
    (v : IsDedekindDomain.HeightOneSpectrum R) (r : R) :
    IsUnit (normToValuationIntegers (K := K) v r) ↔ r ∉ v.asIdeal := by
  rw [← not_iff_not]
  simp only [not_not, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change v.valuation K (algebraMap R K r) < 1 ↔ r ∈ v.asIdeal
  rw [v.valuation_of_algebraMap]
  exact v.intValuation_lt_one_iff_mem r

/-- The actual valuation integer ring in the fraction field is the
localization of the original Dedekind domain at its height-one prime. -/
def localizationValuationIntegersEquiv
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal ≃+* (v.valuation K).integer := by
  let A := Localization.AtPrime v.asIdeal
  let B := (v.valuation K).integer
  let g : R →+* B := normToValuationIntegers v
  have hg (s : v.asIdeal.primeCompl) : IsUnit (g s) :=
    (normToValuationIntegers_unit_iff (K := K) v s).mpr s.property
  let f : A →+* B := IsLocalization.lift hg
  have hf_apply (r : R) : f (algebraMap R A r) = g r :=
    IsLocalization.lift_eq hg r
  haveI : IsLocalHom f := ⟨by
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl x
    apply (IsLocalization.AtPrime.isUnit_mk'_iff A v.asIdeal a s).mpr
    apply (normToValuationIntegers_unit_iff (K := K) v a).mp
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
  have hf_inj : Function.Injective f := by
    intro x y h
    apply FaithfulSMul.algebraMap_injective A K
    change (f x : K) = (f y : K)
    exact congrArg Subtype.val h
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
  exact RingEquiv.ofBijective f ⟨hf_inj, hf_surj⟩

def valuationIntegersResidueEquiv
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    v.asIdeal.ResidueField ≃+* ResidueField (v.valuation K).integer :=
  ResidueField.mapEquiv (localizationValuationIntegersEquiv (K := K) v)

end Localization

variable {K : Type*} [Field K] [NumberField K]

/-- Density preserves the residue field, with an actual ring equivalence. -/
def valuationCompletionResidueEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ResidueField (v.valuation K).integer ≃+* ResidueField (v.adicCompletionIntegers K) := by
  let f := valuationIntegerMap (v.valuation K) (algebraMap K (v.adicCompletion K))
    (fun x : K => v.valuedAdicCompletion_eq_valuation' (K := K) x)
  have hs : Function.Surjective (ResidueField.map f) :=
    residueMap_surjective_of_dense (v.valuation K) (algebraMap K (v.adicCompletion K))
      (fun x : K => v.valuedAdicCompletion_eq_valuation' (K := K) x)
      (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation K)))
  exact RingEquiv.ofBijective (ResidueField.map f) ⟨(ResidueField.map f).injective, hs⟩

/-- The original quotient and completed residue field are isomorphic. -/
def quotientCompletionResidueEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+* ResidueField (v.adicCompletionIntegers K) :=
  (RingEquiv.ofBijective (algebraMap (𝓞 K ⧸ v.asIdeal) v.asIdeal.ResidueField)
    v.asIdeal.bijective_algebraMap_quotient_residueField).trans
      ((valuationIntegersResidueEquiv (K := K) v).trans (valuationCompletionResidueEquiv v))

theorem completion_residue_card_eq_absNorm
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Nat.card (ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_congr (quotientCompletionResidueEquiv v).toEquiv]
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- A natural number vanishes in the completed residue field exactly when
it lies in the original prime ideal. In particular this detects primes over 6. -/
theorem completion_residue_natCast_eq_zero_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (n : ResidueField (v.adicCompletionIntegers K)) = 0 ↔ (n : 𝓞 K) ∈ v.asIdeal := by
  let e := quotientCompletionResidueEquiv v
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.injective
    simpa only [map_natCast, map_zero] using h
  · intro h
    have he := congrArg e (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    simpa only [map_natCast, map_zero] using he

end WaringSiegel

#print axioms WaringSiegel.quotientCompletionResidueEquiv
#print axioms WaringSiegel.completion_residue_card_eq_absNorm

#print axioms WaringSiegel.completion_residue_natCast_eq_zero_iff
