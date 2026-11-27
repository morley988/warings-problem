import WaringSiegel.WSL2LocalRamifiedCount

/-!
# Finite branch seeds for primitive cubic solutions

Approximate primitive solutions at precision `2v(3)+1` lift to exact tuples
without changing their classes modulo `m^(v(3)+1)`. Consequently the relevant
classes form one finite set independent of the later counting precision.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

theorem cube_tuple_lift_stability
    {R : Type*} [CommRing R] [HenselianLocalRing R] {s : ℕ}
    (x : Fin s → R) (hx : ∃ i, IsUnit (x i)) {a : R}
    (ha : a - (∑ i, x i ^ 3) ∈ cubicStabilityIdeal R) :
    ∃ y : Fin s → R, (∑ i, y i ^ 3) = a ∧
      (∀ i, y i - x i ∈ cubicBranchIdeal R) ∧ ∃ i, IsUnit (y i) := by
  classical
  obtain ⟨j, hj⟩ := hx
  let b : R := a - ∑ i ∈ Finset.univ.erase j, x i ^ 3
  have hb : b - x j ^ 3 ∈ cubicStabilityIdeal R := by
    have he : b - x j ^ 3 = a - (∑ i, x i ^ 3) := by
      dsimp [b]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      ring
    rwa [he]
  obtain ⟨z, hz, hzx⟩ := unit_cube_stability_branch hj hb
  have hzunit : IsUnit z := by
    apply (residue_ne_zero_iff_isUnit z).mp
    have hres : residue R z = residue R (x j) := Ideal.Quotient.eq.mpr
      (Ideal.mul_le_left hzx)
    rw [hres]
    exact (residue_ne_zero_iff_isUnit (x j)).mpr hj
  refine ⟨Function.update x j z, ?_, ?_, j, by simpa using hzunit⟩
  · have hpow : (fun i => (Function.update x j z i) ^ 3) =
        Function.update (fun i => x i ^ 3) j (z ^ 3) := by
      ext i
      by_cases hi : i = j <;> simp only [Function.update_apply, hi, if_true, if_false]
    rw [hpow, Finset.sum_update_of_mem (Finset.mem_univ j), hz]
    simp only [b, Finset.sdiff_singleton_eq_erase]
    abel
  · intro i
    by_cases hi : i = j
    · subst i
      simpa only [Function.update_self] using hzx
    · simp only [Function.update_of_ne hi, sub_self, Ideal.zero_mem]

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem cubic_branch_precision_le (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : cubicDerivativeOrder R + 1 ≤ cubicLocalPrecision R := by
  dsimp [cubicDerivativeOrder, cubicLocalPrecision]
  omega

def PrimitiveCubicBranchSeeds (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (s : ℕ) (a : R) :=
  {α : Fin s → R ⧸ maximalIdeal R ^ (cubicDerivativeOrder R + 1) //
    ∃ y : Fin s → R, (∑ i, y i ^ 3) = a ∧
      (∀ i, Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (y i) = α i) ∧
        ∃ i, IsUnit (y i)}

instance primitiveCubicBranchSeeds_finite [Finite (ResidueField R)] (s : ℕ) (a : R) :
    Finite (PrimitiveCubicBranchSeeds R s a) := by
  letI := dvr_power_quotient_finite (R := R) (cubicDerivativeOrder R + 1)
  unfold PrimitiveCubicBranchSeeds
  infer_instance

theorem primitive_quotient_lifts_to_branch_seed [HenselianLocalRing R]
    (h3 : (3 : R) ≠ 0) (e : ℕ) (he : cubicLocalPrecision R ≤ e)
    (s : ℕ) (a : R)
    (x : PrimitiveLocalCubicSolutions R (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by have := cubicLocalPrecision_pos R; omega)) s a) :
    ∃ y : Fin s → R, (∑ i, y i ^ 3) = a ∧
      (∀ i, Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (y i) =
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (by
          exact (cubic_branch_precision_le R).trans he :
          cubicDerivativeOrder R + 1 ≤ e)) (x.val i)) ∧ ∃ i, IsUnit (y i) := by
  classical
  choose z hz using fun i => Ideal.Quotient.mk_surjective (x.val i)
  have hzu : ∃ i, IsUnit (z i) := by
    obtain ⟨j, hj⟩ := x.property.2
    refine ⟨j, (residue_ne_zero_iff_isUnit (z j)).mp ?_⟩
    have hr : residue R (z j) = localResidueReduction (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by have := cubicLocalPrecision_pos R; omega)) (x.val j) := by
        rw [← hz j]
        rfl
    rwa [hr]
  have hc : a - (∑ i, z i ^ 3) ∈ cubicStabilityIdeal R := by
    have hc0 : (∑ i, z i ^ 3) - a ∈ maximalIdeal R ^ e := by
      apply Ideal.Quotient.eq.mp
      simpa only [map_sum, map_pow, hz] using x.property.1
    have hce : a - (∑ i, z i ^ 3) ∈ maximalIdeal R ^ e := by
      simpa only [neg_sub] using (maximalIdeal R ^ e).neg_mem hc0
    rw [← cubic_stability_ideal_eq_power R h3]
    exact Ideal.pow_le_pow_right he hce
  obtain ⟨y, hy, hyz, hyu⟩ := cube_tuple_lift_stability z hzu hc
  refine ⟨y, hy, ?_, hyu⟩
  intro i
  have hq : Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (y i) =
      Ideal.Quotient.mk _ (z i) := Ideal.Quotient.eq.mpr
    ((cubicBranchIdeal_eq_power R h3) ▸ hyz i)
  rw [hq, ← hz i, Ideal.Quotient.factor_mk]

/-- At adequate precision, all primitive solutions are partitioned by one
finite set of exact branch seeds independent of precision. -/
def primitiveLocalBranchEquiv [HenselianLocalRing R]
    (h3 : (3 : R) ≠ 0) (e : ℕ) (he : cubicLocalPrecision R ≤ e)
    (s : ℕ) (a : R) :
    PrimitiveLocalCubicSolutions R (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by have := cubicLocalPrecision_pos R; omega)) s a ≃
      (Σ α : PrimitiveCubicBranchSeeds R s a,
        LocalCubicIdealClass R e (cubicDerivativeOrder R + 1)
          (by exact (cubic_branch_precision_le R).trans he) s a α.val) where
  toFun x :=
    ⟨⟨fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (by
        exact (cubic_branch_precision_le R).trans he :
        cubicDerivativeOrder R + 1 ≤ e)) (x.val i),
      primitive_quotient_lifts_to_branch_seed h3 e he s a x⟩,
        ⟨x.val, x.property.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.val, x.2.property.1, by
    obtain ⟨y, -, hy, j, hj⟩ := x.1.property
    refine ⟨j, ?_⟩
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (x.2.val j)
    have hq : Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) z =
        Ideal.Quotient.mk _ (y j) := by
      have hh := x.2.property.2 j
      rw [← hz, Ideal.Quotient.factor_mk] at hh
      exact hh.trans (hy j).symm
    have hr : residue R z = residue R (y j) := Ideal.Quotient.eq.mpr
      (Ideal.pow_le_self (Nat.succ_ne_zero _) (Ideal.Quotient.eq.mp hq))
    rw [← hz, localResidueReduction_mk, hr]
    exact (residue_ne_zero_iff_isUnit (y j)).mpr hj⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨α, hα⟩, ⟨x, hx⟩⟩
    have heq : (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (by
        exact (cubic_branch_precision_le R).trans he :
        cubicDerivativeOrder R + 1 ≤ e)) (x i)) = α := funext hx.2
    subst α
    rfl

theorem primitive_local_cubic_count_ramified_exact
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : (3 : R) ≠ 0) (s r : ℕ) (a : R) :
    primitiveLocalCubicSolutionCount R
      (maximalIdeal R ^ ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R))
      (Ideal.pow_le_self (by omega)) (s + 1) a =
      Nat.card (PrimitiveCubicBranchSeeds R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * (r + cubicDerivativeOrder R) + cubicDerivativeOrder R) := by
  classical
  letI := dvr_power_quotient_finite (R := R)
    ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
  letI := Fintype.ofFinite (PrimitiveCubicBranchSeeds R (s + 1) a)
  unfold primitiveLocalCubicSolutionCount
  rw [Nat.card_congr (primitiveLocalBranchEquiv h3 _ (by
    dsimp [cubicLocalPrecision, cubicDerivativeOrder]; omega) _ _), Nat.card_sigma]
  have hc (α : PrimitiveCubicBranchSeeds R (s + 1) a) :
      Nat.card (LocalCubicIdealClass R
        ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
        (cubicDerivativeOrder R + 1) (by omega) (s + 1) a α.val) =
      Nat.card (ResidueField R) ^ (s * (r + cubicDerivativeOrder R) + cubicDerivativeOrder R) := by
    obtain ⟨x, hsum, hclass, hunit⟩ := α.property
    have he := local_cubic_ideal_class_card_of_unit h3 x hunit r
    have hα : (fun i => Ideal.Quotient.mk
        (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (x i)) = α.val := funext hclass
    rwa [hsum, hα] at he
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.cast_id]

end WaringSiegel

#print axioms WaringSiegel.primitive_quotient_lifts_to_branch_seed

#print axioms WaringSiegel.primitive_local_cubic_count_ramified_exact
