import WaringSiegel.WSL3MomentLocalPowerBranchCount
import WaringSiegel.WSL3MomentLocalPowerPrimitive

/-!
# Finite branch seeds for primitive power solutions

Approximate primitive solutions at precision `2v(k)+1` lift to exact tuples
without changing their classes modulo `m^(v(k)+1)`. Consequently the relevant
classes form one finite set independent of the later counting precision.
-/

noncomputable section
set_option maxHeartbeats 1400000

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel.WSL3

theorem power_tuple_lift_stability (k : ℕ) (hk : 0<k)
    {R : Type*} [CommRing R] [HenselianLocalRing R] {s : ℕ}
    (x : Fin s → R) (hx : ∃ i, IsUnit (x i)) {a : R}
    (ha : a - (∑ i, x i ^ k) ∈ powerStabilityIdeal R k) :
    ∃ y : Fin s → R, (∑ i, y i ^ k) = a ∧
      (∀ i, y i - x i ∈ powerBranchIdeal R k) ∧ ∃ i, IsUnit (y i) := by
  classical
  obtain ⟨j, hj⟩ := hx
  let b : R := a - ∑ i ∈ Finset.univ.erase j, x i ^ k
  have hb : b - x j ^ k ∈ powerStabilityIdeal R k := by
    have he : b - x j ^ k = a - (∑ i, x i ^ k) := by
      dsimp [b]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      ring
    rwa [he]
  obtain ⟨z, hz, hzx⟩ := unit_power_stability_branch k hk hj hb
  have hzunit : IsUnit z := by
    apply (residue_ne_zero_iff_isUnit z).mp
    have hres : residue R z = residue R (x j) := Ideal.Quotient.eq.mpr
      (Ideal.mul_le_left hzx)
    rw [hres]
    exact (residue_ne_zero_iff_isUnit (x j)).mpr hj
  refine ⟨Function.update x j z, ?_, ?_, j, by simpa using hzunit⟩
  · have hpow : (fun i => (Function.update x j z i) ^ k) =
        Function.update (fun i => x i ^ k) j (z ^ k) := by
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

theorem power_branch_precision_le (k : ℕ) (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : powerDerivativeOrder R k + 1 ≤ powerLocalPrecision R k := by
  dsimp [powerDerivativeOrder, powerLocalPrecision]
  omega

def PrimitivePowerBranchSeeds (k : ℕ) (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (s : ℕ) (a : R) :=
  {α : Fin s → R ⧸ maximalIdeal R ^ (powerDerivativeOrder R k + 1) //
    ∃ y : Fin s → R, (∑ i, y i ^ k) = a ∧
      (∀ i, Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (y i) = α i) ∧
        ∃ i, IsUnit (y i)}

instance primitivePowerBranchSeeds_finite (k : ℕ) [Finite (ResidueField R)] (s : ℕ) (a : R) :
    Finite (PrimitivePowerBranchSeeds k R s a) := by
  letI := dvr_power_quotient_finite (R := R) (powerDerivativeOrder R k + 1)
  unfold PrimitivePowerBranchSeeds
  infer_instance

theorem primitive_quotient_lifts_to_branch_seed (k : ℕ) (hk : 0<k) [HenselianLocalRing R]
    (hk0 : (k : R) ≠ 0) (e : ℕ) (he : powerLocalPrecision R k ≤ e)
    (s : ℕ) (a : R)
    (x : PrimitiveLocalPowerSolutions k R (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by have := powerLocalPrecision_pos R k; omega)) s a) :
    ∃ y : Fin s → R, (∑ i, y i ^ k) = a ∧
      (∀ i, Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (y i) =
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (by
          exact (power_branch_precision_le k R).trans he :
          powerDerivativeOrder R k + 1 ≤ e)) (x.val i)) ∧ ∃ i, IsUnit (y i) := by
  classical
  choose z hz using fun i => Ideal.Quotient.mk_surjective (x.val i)
  have hzu : ∃ i, IsUnit (z i) := by
    obtain ⟨j, hj⟩ := x.property.2
    refine ⟨j, (residue_ne_zero_iff_isUnit (z j)).mp ?_⟩
    have hr : residue R (z j) = localResidueReduction (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by have := powerLocalPrecision_pos R k; omega)) (x.val j) := by
        rw [← hz j]
        rfl
    rwa [hr]
  have hc : a - (∑ i, z i ^ k) ∈ powerStabilityIdeal R k := by
    have hc0 : (∑ i, z i ^ k) - a ∈ maximalIdeal R ^ e := by
      apply Ideal.Quotient.eq.mp
      simpa only [map_sum, map_pow, hz] using x.property.1
    have hce : a - (∑ i, z i ^ k) ∈ maximalIdeal R ^ e := by
      simpa only [neg_sub] using (maximalIdeal R ^ e).neg_mem hc0
    rw [← power_stability_ideal_eq_power R k hk0]
    exact Ideal.pow_le_pow_right he hce
  obtain ⟨y, hy, hyz, hyu⟩ := power_tuple_lift_stability k hk z hzu hc
  refine ⟨y, hy, ?_, hyu⟩
  intro i
  have hq : Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (y i) =
      Ideal.Quotient.mk _ (z i) := Ideal.Quotient.eq.mpr
    ((powerBranchIdeal_eq_power R k hk0) ▸ hyz i)
  rw [hq, ← hz i, Ideal.Quotient.factor_mk]

/-- At adequate precision, all primitive solutions are partitioned by one
finite set of exact branch seeds independent of precision. -/
def primitiveLocalBranchEquiv (k : ℕ) (hk : 0<k) [HenselianLocalRing R]
    (hk0 : (k : R) ≠ 0) (e : ℕ) (he : powerLocalPrecision R k ≤ e)
    (s : ℕ) (a : R) :
    PrimitiveLocalPowerSolutions k R (maximalIdeal R ^ e)
      (Ideal.pow_le_self (by have := powerLocalPrecision_pos R k; omega)) s a ≃
      (Σ α : PrimitivePowerBranchSeeds k R s a,
        LocalPowerIdealClass k R e (powerDerivativeOrder R k + 1)
          (by exact (power_branch_precision_le k R).trans he) s a α.val) where
  toFun x :=
    ⟨⟨fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (by
        exact (power_branch_precision_le k R).trans he :
        powerDerivativeOrder R k + 1 ≤ e)) (x.val i),
      primitive_quotient_lifts_to_branch_seed k hk hk0 e he s a x⟩,
        ⟨x.val, x.property.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.val, x.2.property.1, by
    obtain ⟨y, -, hy, j, hj⟩ := x.1.property
    refine ⟨j, ?_⟩
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (x.2.val j)
    have hq : Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) z =
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
        exact (power_branch_precision_le k R).trans he :
        powerDerivativeOrder R k + 1 ≤ e)) (x i)) = α := funext hx.2
    subst α
    rfl

theorem primitive_local_power_count_ramified_exact (k : ℕ) (hk : 0<k)
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk0 : (k : R) ≠ 0) (s r : ℕ) (a : R) :
    primitiveLocalPowerSolutionCount k R
      (maximalIdeal R ^ ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k))
      (Ideal.pow_le_self (by omega)) (s + 1) a =
      Nat.card (PrimitivePowerBranchSeeds k R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * (r + powerDerivativeOrder R k) + powerDerivativeOrder R k) := by
  classical
  letI := dvr_power_quotient_finite (R := R)
    ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
  letI := Fintype.ofFinite (PrimitivePowerBranchSeeds k R (s + 1) a)
  unfold primitiveLocalPowerSolutionCount
  rw [Nat.card_congr (primitiveLocalBranchEquiv k hk hk0 _ (by
    dsimp [powerLocalPrecision, powerDerivativeOrder]; omega) _ _), Nat.card_sigma]
  have hc (α : PrimitivePowerBranchSeeds k R (s + 1) a) :
      Nat.card (LocalPowerIdealClass k R
        ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
        (powerDerivativeOrder R k + 1) (by omega) (s + 1) a α.val) =
      Nat.card (ResidueField R) ^ (s * (r + powerDerivativeOrder R k) + powerDerivativeOrder R k) := by
    obtain ⟨x, hsum, hclass, hunit⟩ := α.property
    have he := local_power_ideal_class_card_of_unit k hk hk0 x hunit r
    have hα : (fun i => Ideal.Quotient.mk
        (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (x i)) = α.val := funext hclass
    rwa [hsum, hα] at he
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.cast_id]

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.primitive_quotient_lifts_to_branch_seed

#print axioms WaringSiegel.WSL3.primitive_local_power_count_ramified_exact
