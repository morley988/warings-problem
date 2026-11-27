import WaringSiegel.WSL3ConductorCoefficient
import WaringSiegel.WSL3ConductorEulerBase

/-! # WSL3: absolute convergence of the actual ideal conductor series -/
noncomputable section
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def idealPrimeExponent (I : Ideal (𝓞 K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

def idealPrimeSupport (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors hI).toFinset

theorem idealPrimeExponent_pos_of_mem (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : v ∈ idealPrimeSupport I hI) :
    0 < idealPrimeExponent I v := by
  apply Nat.pos_of_ne_zero
  exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).mpr
    ((Ideal.finite_factors hI).mem_toFinset.mp hv)

theorem idealPrimeSupport_factorization (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (∏ v ∈ idealPrimeSupport I hI, v.asIdeal^idealPrimeExponent I v) = I := by
  have h := Ideal.finprod_heightOneSpectrum_factorization hI
  rw [finprod_eq_finset_prod_of_mulSupport_subset
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => v.maxPowDividing I)
    (s := idealPrimeSupport I hI)] at h
  · exact h
  · intro v hv
    apply (Ideal.finite_factors hI).mem_toFinset.mpr
    apply (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp
    intro hz
    exact hv (by simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hz])

def nonzeroIdealConductorGraph (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ) :=
  (idealPrimeSupport I.1 I.2).image (fun v => (v,idealPrimeExponent I.1 v - 1))

theorem nonzeroIdealConductorGraph_product (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    (∏ ve ∈ nonzeroIdealConductorGraph I, ve.1.asIdeal^(ve.2+1)) = I.1 := by
  unfold nonzeroIdealConductorGraph
  rw [Finset.prod_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  calc
    _ = ∏ v ∈ idealPrimeSupport I.1 I.2, v.asIdeal^idealPrimeExponent I.1 v := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [Nat.sub_add_cancel (idealPrimeExponent_pos_of_mem I.1 I.2 v hv)]
    _ = I.1 := idealPrimeSupport_factorization I.1 I.2

theorem nonzeroIdealConductorGraph_injective :
    Function.Injective (nonzeroIdealConductorGraph (K := K)) := by
  intro I J h
  apply Subtype.ext
  rw [← nonzeroIdealConductorGraph_product I, ← nonzeroIdealConductorGraph_product J, h]

theorem idealPrimitiveCubicCoefficient_eq_graph_product
    (I : {I : Ideal (𝓞 K) // I ≠ 0}) (ν : 𝓞 K) :
    idealPrimitiveCubicCoefficient I.1 I.2 ν =
      ∏ ve ∈ nonzeroIdealConductorGraph I,
        primePowerPrimitiveCubicCoefficient ve.1 (ve.2+1) ν := by
  have h := idealPrimitiveCubicCoefficient_finset_prod
    (idealPrimeSupport I.1 I.2) (idealPrimeExponent I.1) ν
  simp only [idealPrimeSupport_factorization] at h
  rw [h]
  unfold nonzeroIdealConductorGraph
  rw [Finset.prod_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  apply Finset.prod_congr rfl
  intro v hv
  rw [Nat.sub_add_cancel (idealPrimeExponent_pos_of_mem I.1 I.2 v hv)]

/-- Absolute convergence of the literal exact-conductor series over every
nonzero integral ideal. No Euler-product identity is assumed. -/
theorem idealPrimitiveCubicCoefficient_norm_summable
    {ν : 𝓞 K} (hν : ν ≠ 0) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) := by
  have hs := summable_norm_finset_products
    (fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
      primePowerPrimitiveCubicCoefficient ve.1 (ve.2+1) ν)
    (primePowerPrimitiveCubicCoefficient_pair_norm_summable hν)
  have h := hs.comp_injective (nonzeroIdealConductorGraph_injective (K := K))
  apply h.congr
  intro I
  exact congrArg norm (idealPrimitiveCubicCoefficient_eq_graph_product I ν).symm

end WaringSiegel

#print axioms WaringSiegel.idealPrimitiveCubicCoefficient_norm_summable
