import WaringSiegel.WSL2LocalResidueNorm
import WaringSiegel.WSL2LocalCubeKernel

/-!
# Original prime-power quotients and completed local quotients

Membership in powers of the original prime is detected by the preserved
integer-valued valuation. The induced quotient map is injective, and equal
finite cardinalities make it an isomorphism at every exponent.
-/

noncomputable section

open IsLocalRing
open scoped NumberField WithZero

namespace WaringSiegel

private theorem withZeroMulInt_lt_one_iff_le_neg_one (z : ℤᵐ⁰) :
    z < 1 ↔ z ≤ WithZero.exp (-1 : ℤ) := by
  induction z using WithZero.recZeroCoe with
  | zero => simp
  | coe z =>
    change (↑z : ℤᵐ⁰) < ((1 : Multiplicative ℤ) : ℤᵐ⁰) ↔
      (↑z : ℤᵐ⁰) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)
    rw [WithZero.coe_lt_coe, WithZero.coe_le_coe]
    change z.toAdd < 0 ↔ z.toAdd ≤ -1
    omega

variable {K : Type*} [Field K] [NumberField K]

/-- The completion embedding preserves every prime-power membership test. -/
theorem completion_mem_maximalIdeal_pow_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (n : ℕ) :
    algebraMap (𝓞 K) (v.adicCompletionIntegers K) r ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ n ↔ r ∈ v.asIdeal ^ n := by
  let R := v.adicCompletionIntegers K
  let w : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  have hw := Valuation.valuationSubring.integers w
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let π' : R := algebraMap (𝓞 K) R π
  have hπval : w (π' : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) π) = _
    rw [v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]
    exact hπ
  have hm : maximalIdeal R = Ideal.span ({π'} : Set R) := by
    ext x
    rw [Ideal.mem_span_singleton, hw.dvd_iff_le]
    change x ∈ maximalIdeal R ↔ w (x : v.adicCompletion K) ≤ w (π' : v.adicCompletion K)
    have hxval : x ∈ maximalIdeal R ↔ w (x : v.adicCompletion K) < 1 :=
      Valuation.mem_maximalIdeal_iff (v.adicCompletion K) w
    rw [hxval, hπval]
    exact withZeroMulInt_lt_one_iff_le_neg_one _
  change algebraMap (𝓞 K) R r ∈ maximalIdeal R ^ n ↔ _
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hw.dvd_iff_le]
  change w (algebraMap (𝓞 K) (v.adicCompletion K) r) ≤ w ((π' : v.adicCompletion K) ^ n) ↔ _
  rw [map_pow, hπval]
  have hp : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) ^ n = WithZero.exp (-(n : ℤ)) := by
    rw [← WithZero.exp_nsmul]
    congr 1
    simp
  rw [hp]
  change Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r) ≤
    WithZero.exp (-(n : ℤ)) ↔ _
  rw [v.valuedAdicCompletion_eq_valuation, v.valuation_of_algebraMap]
  exact v.intValuation_le_pow_iff_mem r n

/-- The actual completion embedding descends to each original prime-power quotient. -/
def primePowerCompletionMap
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (𝓞 K ⧸ v.asIdeal ^ n) →+*
      ((v.adicCompletionIntegers K) ⧸ maximalIdeal (v.adicCompletionIntegers K) ^ n) :=
  Ideal.Quotient.lift (v.asIdeal ^ n)
    ((Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ n)).comp
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K))) (by
    intro r hr
    change Ideal.Quotient.mk _ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((completion_mem_maximalIdeal_pow_iff v r n).mpr hr))

@[simp] theorem primePowerCompletionMap_mk
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) (r : 𝓞 K) :
    primePowerCompletionMap v n (Ideal.Quotient.mk (v.asIdeal ^ n) r) =
      Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) r) := rfl

theorem primePowerCompletionMap_injective
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Injective (primePowerCompletionMap v n) := by
  intro x y h
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  rw [primePowerCompletionMap_mk, primePowerCompletionMap_mk] at h
  have hd := Ideal.Quotient.eq.mp h
  rw [← map_sub] at hd
  exact (completion_mem_maximalIdeal_pow_iff v (r - s) n).mp hd

theorem primePower_completion_quotient_card_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (𝓞 K ⧸ v.asIdeal ^ n) =
      Nat.card ((v.adicCompletionIntegers K) ⧸ maximalIdeal (v.adicCompletionIntegers K) ^ n) := by
  calc
    Nat.card (𝓞 K ⧸ v.asIdeal ^ n) = Ideal.absNorm (v.asIdeal ^ n) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = (Ideal.absNorm v.asIdeal) ^ n := map_pow Ideal.absNorm _ _
    _ = Nat.card (ResidueField (v.adicCompletionIntegers K)) ^ n := by
      rw [completion_residue_card_eq_absNorm]
    _ = Nat.card ((v.adicCompletionIntegers K) ⧸
        maximalIdeal (v.adicCompletionIntegers K) ^ n) :=
      (dvr_power_quotient_card n).symm

/-- Original and completed prime-power quotients are canonically isomorphic. -/
def primePowerCompletionEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (𝓞 K ⧸ v.asIdeal ^ n) ≃+*
      ((v.adicCompletionIntegers K) ⧸ maximalIdeal (v.adicCompletionIntegers K) ^ n) := by
  letI := completionIntegers_residueFinite v
  letI := dvr_power_quotient_finite (R := v.adicCompletionIntegers K) n
  exact RingEquiv.ofBijective (primePowerCompletionMap v n)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨primePowerCompletionMap_injective v n, primePower_completion_quotient_card_eq v n⟩)

/-- The unit-cubing kernel is invariant under a multiplicative equivalence. -/
theorem cubeUnitKernelCard_congr {A B : Type*} [Monoid A] [Monoid B]
    (e : A ≃* B) : cubeUnitKernelCard A = cubeUnitKernelCard B := by
  unfold cubeUnitKernelCard
  let eu := Units.mapEquiv e
  apply Nat.card_congr
  exact eu.toEquiv.subtypeEquiv (fun u => by
    change u ^ 3 = 1 ↔ eu u ^ 3 = 1
    rw [← map_pow, ← map_one eu, eu.injective.eq_iff])

theorem completion_three_isUnit_iff
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsUnit (3 : v.adicCompletionIntegers K) ↔ (3 : 𝓞 K) ∉ v.asIdeal := by
  rw [← residue_ne_zero_iff_isUnit]
  simpa only [map_ofNat] using not_congr (completion_residue_natCast_eq_zero_iff v 3)

/-- The actual original prime-power quotient has an exponent-independent cube-kernel bound. -/
theorem primePower_cube_unit_kernel_uniform_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    cubeUnitKernelCard (𝓞 K ⧸ v.asIdeal ^ e) ≤
      (Ideal.absNorm v.asIdeal) ^ cubicLocalPrecision (v.adicCompletionIntegers K) := by
  rw [cubeUnitKernelCard_congr (primePowerCompletionEquiv v e).toMulEquiv]
  simpa only [completion_residue_card_eq_absNorm] using
    completion_cube_unit_kernel_uniform_bound v e

/-- Away from the primes over 3 the actual cube kernel is at most three. -/
theorem primePower_cube_unit_kernel_le_three
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h3 : (3 : 𝓞 K) ∉ v.asIdeal) (e : ℕ) :
    cubeUnitKernelCard (𝓞 K ⧸ v.asIdeal ^ e) ≤ 3 := by
  rw [cubeUnitKernelCard_congr (primePowerCompletionEquiv v e).toMulEquiv]
  exact completion_cube_unit_kernel_le_three v ((completion_three_isUnit_iff v).mpr h3) e

end WaringSiegel

#print axioms WaringSiegel.completion_mem_maximalIdeal_pow_iff

#print axioms WaringSiegel.primePowerCompletionEquiv
#print axioms WaringSiegel.primePower_cube_unit_kernel_uniform_bound
#print axioms WaringSiegel.primePower_cube_unit_kernel_le_three
