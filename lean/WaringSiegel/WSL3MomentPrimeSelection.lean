import WaringSiegel.WSL3MomentPrimitive
import WaringSiegel.WSL2MomentDegreeOneQuotient
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Large unramified residue-degree-one primes

The prime is selected from an actual integral generator with nonzero
conductor exponent. A simple linear factor gives residue degree and
ramification index one through Kummer--Dedekind.
-/

noncomputable section
open Polynomial Algebra IntermediateField Ideal NumberField
open scoped NumberField WithZero Classical

namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem integral_minpoly_rational_coprime_derivative (θ : 𝓞 K) :
    IsCoprime ((minpoly ℤ θ).map (algebraMap ℤ ℚ))
      ((minpoly ℤ θ).derivative.map (algebraMap ℤ ℚ)) := by
  rw [← Polynomial.derivative_map,
    ← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral]
  exact Algebra.IsSeparable.isSeparable ℚ (algebraMap (𝓞 K) K θ)

theorem simple_root_linear_multiplicity {F : Type*} [Field F]
    (f : F[X]) (hf : f ≠ 0) (a : F)
    (ha : f.eval a = 0) (ha' : f.derivative.eval a ≠ 0) :
    multiplicity (X - C a) f = 1 := by
  have hpos : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf).mpr ha
  have hle : f.rootMultiplicity a ≤ 1 := by
    by_contra h
    have hd := ((one_lt_rootMultiplicity_iff_isRoot (t := a) hf).mp (by omega)).2
    exact ha' hd
  have heq : f.rootMultiplicity a = 1 := by omega
  simpa only [rootMultiplicity_eq_multiplicity, if_neg hf] using heq

theorem intValuation_eq_one_of_mem_not_mem_sq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx0 : x ≠ 0) (hx : x ∈ v.asIdeal) (hx2 : x ∉ v.asIdeal ^ 2) :
    v.intValuation x = WithZero.exp (-1 : ℤ) := by
  have h1 := (v.intValuation_le_pow_iff_mem x 1).mpr (by simpa using hx)
  have h2 := (v.intValuation_le_pow_iff_mem x 2).not.mpr hx2
  rw [v.intValuation_if_neg hx0] at h1 h2 ⊢
  simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le, Nat.cast_one,
    Nat.cast_ofNat, neg_le_neg_iff] at h1 h2
  congr 2
  omega

/-- An actual degree-one unramified prime above a rational prime larger than
any prescribed bound. No prime-existence assumption remains. -/
theorem exists_large_unramified_degreeOne_prime (k : ℕ) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧
      ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Ideal.absNorm v.asIdeal = p ∧
        v.intValuation (p : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨θ, hθ⟩ := exists_integral_generator_nonzero_exponent (K := K)
  obtain ⟨p, hp, hpk, hpe, a, ha, ha'⟩ :=
    WSL2.polynomial_large_simple_root_mod (minpoly ℤ θ)
      (minpoly.natDegree_pos θ.isIntegral)
      (integral_minpoly_rational_coprime_derivative θ)
      (RingOfIntegers.exponent θ : ℤ) (by exact_mod_cast hθ) k
  letI : Fact p.Prime := ⟨hp⟩
  have hpe' : ¬ p ∣ RingOfIntegers.exponent θ := by
    exact_mod_cast hpe
  let f : (ZMod p)[X] := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hf : f ≠ 0 := map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have hfac : X - C a ∈ RingOfIntegers.monicFactorsMod θ p := by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hf]
    exact ⟨irreducible_X_sub_C a, monic_X_sub_C a, (dvd_iff_isRoot).mpr ha⟩
  let P : Ideal (𝓞 K) :=
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hpe').symm ⟨X - C a, hfac⟩
  have hprime : P.IsPrime :=
    ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hpe').symm
      ⟨X - C a, hfac⟩).property.1
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hpe').symm
      ⟨X - C a, hfac⟩).property.2
  have hinertia : (Ideal.span {(p : ℤ)}).inertiaDeg P = 1 := by
    simpa [P] using
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hpe' hfac
  have hnorm : Ideal.absNorm P = p := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg (p := (p : ℤ)) P
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)),
      hinertia]
    simp
  have hP0 : P ≠ ⊥ := by
    intro h
    have hz : 0 = p := by simpa [h] using hnorm
    exact hp.ne_zero hz.symm
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hprime, hP0⟩
  have hram : Ideal.ramificationIdx (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) P = 1 := by
    rw [NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hpe' hfac]
    exact simple_root_linear_multiplicity f hf a ha (by simpa [f, Polynomial.derivative_map] using ha')
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) =
      Ideal.span {(p : 𝓞 K)} := by simp [Ideal.map_span]
  have hle : Ideal.span {(p : 𝓞 K)} ≤ P := by
    have h := Ideal.le_pow_ramificationIdx
      (f := algebraMap ℤ (𝓞 K)) (p := Ideal.span {(p : ℤ)}) (P := P)
    simpa only [hram, pow_one, hmap] using h
  have hnle : ¬ Ideal.span {(p : 𝓞 K)} ≤ P ^ 2 := by
    rw [← hmap]
    exact (Ideal.ramificationIdx_ne_one_iff (by simpa only [hmap] using hle)).not.mp
      (by simp only [hram, not_ne_iff])
  refine ⟨p, hp, hpk, v, hnorm, ?_⟩
  exact intValuation_eq_one_of_mem_not_mem_sq v (p : 𝓞 K)
    (by exact_mod_cast hp.ne_zero)
    (hle (Ideal.subset_span (Set.mem_singleton _)))
    (fun h => hnle (Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff] using h)))

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.exists_large_unramified_degreeOne_prime
