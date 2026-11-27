import WaringSiegel.WSL2LocalAllPrimeConvergence
import WaringSiegel.WSL2LocalFiniteMoment

/-!
# Uniform cube kernels over prime-power local quotients

The cardinality of the kernel of cubing on units is at most three away from
3, and is bounded independently of the quotient exponent at every prime.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators Classical

namespace WaringSiegel

def cubeUnitKernelCard (A : Type*) [Monoid A] : ℕ := Nat.card {u : Aˣ // u ^ 3 = 1}

theorem cubeUnitKernelCard_le_card (A : Type*) [Monoid A] [Finite A] :
    cubeUnitKernelCard A ≤ Nat.card A := by
  unfold cubeUnitKernelCard
  apply Nat.card_le_card_of_injective (f := fun u : {u : Aˣ // u ^ 3 = 1} => (u.val : A))
  intro u v h
  exact Subtype.ext (Units.ext h)

theorem cubeUnitKernelCard_le_single_cube_count
    {R : Type*} [CommRing R] (I : Ideal R) [Finite (R ⧸ I)] :
    cubeUnitKernelCard (R ⧸ I) ≤ localCubicSolutionCount R I 1 1 := by
  let f : {u : (R ⧸ I)ˣ // u ^ 3 = 1} → LocalCubicSolutions R I 1 1 :=
    fun u => ⟨fun _ => (u.val : R ⧸ I), by
      have hu := congrArg (fun v : (R ⧸ I)ˣ => (v : R ⧸ I)) u.property
      simpa only [Fin.sum_univ_one, Units.val_pow_eq_pow_val, Units.val_one, map_one] using hu⟩
  apply Nat.card_le_card_of_injective (f := f)
  intro u v h
  apply Subtype.ext
  apply Units.ext
  exact congrFun (congrArg (fun x : LocalCubicSolutions R I 1 1 => x.val) h) 0

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem one_cube_branch_seed_card_le :
    Nat.card (PrimitiveCubicBranchSeeds R 1 1) ≤
      Nat.card (ResidueField R) ^ (cubicDerivativeOrder R + 1) := by
  letI := dvr_power_quotient_finite (R := R) (cubicDerivativeOrder R + 1)
  have h := Nat.card_le_card_of_injective
    (f := fun α : PrimitiveCubicBranchSeeds R 1 1 => α.val) Subtype.val_injective
  simpa only [Nat.card_fun, Nat.card_fin, pow_one, dvr_power_quotient_card] using h

/-- A single cube root of 1 is bounded uniformly over all quotient exponents. -/
theorem local_single_cube_count_uniform_bound
    (h3 : (3 : R) ≠ 0) (e : ℕ) :
    localCubicSolutionCount R (maximalIdeal R ^ e) 1 1 ≤
      Nat.card (ResidueField R) ^ cubicLocalPrecision R := by
  letI := dvr_power_quotient_finite (R := R) e
  by_cases he : cubicLocalPrecision R ≤ e
  · have he0 : e ≠ 0 := by have := cubicLocalPrecision_pos R; omega
    have hr : e = (cubicDerivativeOrder R + 1 + (e - cubicLocalPrecision R)) +
        cubicDerivativeOrder R := by
      change 2 * cubicDerivativeOrder R + 1 ≤ e at he
      change e = cubicDerivativeOrder R + 1 + (e - (2 * cubicDerivativeOrder R + 1)) +
        cubicDerivativeOrder R
      omega
    have hc : localCubicSolutionCount R (maximalIdeal R ^ e) 1 1 =
        primitiveLocalCubicSolutionCount R (maximalIdeal R ^ e)
          (Ideal.pow_le_self he0) 1 1 := by
      unfold localCubicSolutionCount primitiveLocalCubicSolutionCount
      exact Nat.card_congr (unitTargetPrimitiveCubicSolutionsEquiv _ _ _ isUnit_one)
    rw [hc, primitive_local_cubic_count_ramified_at h3 0 (e - cubicLocalPrecision R) e hr]
    simp only [zero_mul, zero_add]
    calc
      Nat.card (PrimitiveCubicBranchSeeds R 1 1) * Nat.card (ResidueField R) ^ cubicDerivativeOrder R ≤
        Nat.card (ResidueField R) ^ (cubicDerivativeOrder R + 1) *
          Nat.card (ResidueField R) ^ cubicDerivativeOrder R :=
        Nat.mul_le_mul_right _ one_cube_branch_seed_card_le
      _ = Nat.card (ResidueField R) ^ cubicLocalPrecision R := by
        rw [← pow_add]
        congr 1
        change cubicDerivativeOrder R + 1 + cubicDerivativeOrder R = 2 * cubicDerivativeOrder R + 1
        omega
  · have hc : localCubicSolutionCount R (maximalIdeal R ^ e) 1 1 ≤
        Nat.card (R ⧸ maximalIdeal R ^ e) := by
      have h := Nat.card_le_card_of_injective
        (f := fun x : LocalCubicSolutions R (maximalIdeal R ^ e) 1 1 => x.val)
        Subtype.val_injective
      simpa only [Nat.card_fun, Nat.card_fin, pow_one] using h
    apply hc.trans
    rw [dvr_power_quotient_card]
    exact Nat.pow_le_pow_right Nat.card_pos (Nat.le_of_lt (Nat.lt_of_not_ge he))

theorem cubeUnitKernelCard_local_uniform_bound
    (h3 : (3 : R) ≠ 0) (e : ℕ) :
    cubeUnitKernelCard (R ⧸ maximalIdeal R ^ e) ≤
      Nat.card (ResidueField R) ^ cubicLocalPrecision R := by
  letI := dvr_power_quotient_finite (R := R) e
  exact (cubeUnitKernelCard_le_single_cube_count _).trans
    (local_single_cube_count_uniform_bound h3 e)

/-- Away from 3 the cube kernel is at most three at every local precision. -/
theorem cubeUnitKernelCard_local_le_three
    (h3 : IsUnit (3 : R)) (e : ℕ) :
    cubeUnitKernelCard (R ⧸ maximalIdeal R ^ e) ≤ 3 := by
  letI := dvr_power_quotient_finite (R := R) e
  by_cases he : e = 0
  · subst e
    have h : cubeUnitKernelCard (R ⧸ maximalIdeal R ^ 0) ≤ 1 := by
      apply (cubeUnitKernelCard_le_card (R ⧸ maximalIdeal R ^ 0)).trans_eq
      rw [dvr_power_quotient_card, pow_zero]
    exact h.trans (by decide)
  · let ρ := localResidueReduction (maximalIdeal R ^ e) (Ideal.pow_le_self he)
    have hpow (u : {u : (R ⧸ maximalIdeal R ^ e)ˣ // u ^ 3 = 1}) :
        (u.val : R ⧸ maximalIdeal R ^ e) ^ 3 = 1 := by
      have h := congrArg (fun v : (R ⧸ maximalIdeal R ^ e)ˣ =>
        (v : R ⧸ maximalIdeal R ^ e)) u.property
      simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
    let f : {u : (R ⧸ maximalIdeal R ^ e)ˣ // u ^ 3 = 1} →
        {z : ResidueField R // z ^ 3 = 1} :=
      fun u => ⟨ρ u.val, by simpa only [map_pow, map_one] using congrArg ρ (hpow u)⟩
    have hf : Function.Injective f := by
      intro u v h
      have hr : ρ u.val = ρ v.val :=
        congrArg (fun z : {z : ResidueField R // z ^ 3 = 1} => z.val) h
      have hru : ρ u.val ≠ 0 := by
        intro hz
        have hp := (f u).property
        change (ρ u.val) ^ 3 = 1 at hp
        rw [hz, zero_pow (by decide : 3 ≠ 0)] at hp
        exact zero_ne_one hp
      have heq := (cube_eq_iff_of_same_nonzero_residue h3
        (maximalIdeal R ^ e) (Ideal.pow_le_self he) hr hru).mp
          ((hpow u).trans (hpow v).symm)
      exact Subtype.ext (Units.ext heq)
    have hk := Nat.card_le_card_of_injective f hf
    have hroot : Nat.card {z : ResidueField R // z ^ 3 = 1} ≤ 3 := by
      letI := Fintype.ofFinite (ResidueField R)
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact finite_field_cube_fiber_card (1 : ResidueField R)
    exact hk.trans hroot

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem completion_cube_unit_kernel_uniform_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    cubeUnitKernelCard ((v.adicCompletionIntegers K) ⧸
      maximalIdeal (v.adicCompletionIntegers K) ^ e) ≤
        Nat.card (ResidueField (v.adicCompletionIntegers K)) ^
          cubicLocalPrecision (v.adicCompletionIntegers K) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  exact cubeUnitKernelCard_local_uniform_bound (by norm_num) e

theorem completion_cube_unit_kernel_le_three
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h3 : IsUnit (3 : v.adicCompletionIntegers K)) (e : ℕ) :
    cubeUnitKernelCard ((v.adicCompletionIntegers K) ⧸
      maximalIdeal (v.adicCompletionIntegers K) ^ e) ≤ 3 := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  exact cubeUnitKernelCard_local_le_three h3 e

end WaringSiegel

#print axioms WaringSiegel.cubeUnitKernelCard_local_uniform_bound

#print axioms WaringSiegel.completion_cube_unit_kernel_uniform_bound
#print axioms WaringSiegel.completion_cube_unit_kernel_le_three
