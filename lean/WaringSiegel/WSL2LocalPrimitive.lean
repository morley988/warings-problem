import WaringSiegel.WSL2LocalGoodPrime

/-!
# Exact primitive local densities

This file counts literal cubic solution tuples having at least one nonzero
residue coordinate. Away from 3 their normalized count is constant at every
positive precision, hence its limit exists without an analytic hypothesis.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

def PrimitiveCubicResidues
    (R : Type*) [CommRing R] [IsLocalRing R] (s : ℕ) (a : R) :=
  {α : Fin s → ResidueField R // (∑ i, α i ^ 3) = residue R a ∧ ∃ i, α i ≠ 0}

def PrimitiveLocalCubicSolutions
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ 3) = Ideal.Quotient.mk I a ∧
    ∃ i, localResidueReduction I hI (x i) ≠ 0}

def primitiveLocalCubicSolutionCount
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) : ℕ :=
  Nat.card (PrimitiveLocalCubicSolutions R I hI s a)

instance primitiveCubicResidues_finite
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    (s : ℕ) (a : R) : Finite (PrimitiveCubicResidues R s a) := by
  unfold PrimitiveCubicResidues
  infer_instance

instance primitiveLocalCubicSolutions_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    Finite (PrimitiveLocalCubicSolutions R I hI s a) := by
  unfold PrimitiveLocalCubicSolutions
  infer_instance

instance localCubicResidueClass_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R)
    (α : Fin s → ResidueField R) : Finite (LocalCubicResidueClass R I hI s a α) := by
  unfold LocalCubicResidueClass
  infer_instance

/-- Partition actual primitive quotient tuples by their residue tuple. -/
def primitiveLocalCubicSolutionsEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :
    PrimitiveLocalCubicSolutions R I hI s a ≃
      (Σ α : PrimitiveCubicResidues R s a, LocalCubicResidueClass R I hI s a α.val) where
  toFun x :=
    ⟨⟨fun i => localResidueReduction I hI (x.val i), by
        simpa only [map_sum, map_pow, localResidueReduction_mk] using
          congrArg (localResidueReduction I hI) x.property.1, x.property.2⟩,
      ⟨x.val, x.property.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.val, x.2.property.1, by
    obtain ⟨i, hi⟩ := x.1.property.2
    exact ⟨i, (x.2.property.2 i) ▸ hi⟩⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨α, hα⟩, ⟨x, hx⟩⟩
    have he : (fun i => localResidueReduction I hI (x i)) = α := funext hx.2
    subst α
    rfl

/-- Every primitive residue solution contributes exactly `q^(s*n)` lifts. -/
theorem primitive_local_cubic_count_exact
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s n : ℕ) (a : R) :
    primitiveLocalCubicSolutionCount R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a =
      Nat.card (PrimitiveCubicResidues R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * n) := by
  classical
  letI := dvr_power_quotient_finite (R := R) (n + 1)
  letI := Fintype.ofFinite (PrimitiveCubicResidues R (s + 1) a)
  unfold primitiveLocalCubicSolutionCount
  rw [Nat.card_congr (primitiveLocalCubicSolutionsEquiv _ _ _ _), Nat.card_sigma]
  have hc (α : PrimitiveCubicResidues R (s + 1) a) :
      Nat.card (LocalCubicResidueClass R (maximalIdeal R ^ (n + 1))
        (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α.val) =
        Nat.card (ResidueField R) ^ (s * n) :=
    localCubicResidueClass_card_of_nonzero h3 a α.val α.property.1 α.property.2 n
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.cast_id]

def normalizedPrimitiveLocalCubicCount
    (R : Type*) [CommRing R] [IsLocalRing R] (s n : ℕ) (a : R) : ℝ :=
  (primitiveLocalCubicSolutionCount R (maximalIdeal R ^ (n + 1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) s a : ℝ) /
      (Nat.card (ResidueField R) : ℝ) ^ ((s - 1) * (n + 1))

/-- The primitive normalized sequence is exactly constant away from 3. -/
theorem normalized_primitive_local_cubic_count_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s n : ℕ) (a : R) :
    normalizedPrimitiveLocalCubicCount R (s + 1) n a =
      (Nat.card (PrimitiveCubicResidues R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ResidueField R)).ne'
  unfold normalizedPrimitiveLocalCubicCount
  rw [primitive_local_cubic_count_exact h3]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.add_sub_cancel, Nat.mul_add,
    Nat.mul_one, pow_add]
  simpa only [mul_comm ((Nat.card (ResidueField R) : ℝ) ^ s)] using
    (mul_div_mul_right (Nat.card (PrimitiveCubicResidues R (s + 1) a) : ℝ)
      ((Nat.card (ResidueField R) : ℝ) ^ s) (pow_ne_zero (s * n) hq))

theorem normalized_primitive_local_cubic_count_tendsto
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s : ℕ) (a : R) :
    Filter.Tendsto (fun n => normalizedPrimitiveLocalCubicCount R (s + 1) n a)
      Filter.atTop (nhds ((Nat.card (PrimitiveCubicResidues R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s)) := by
  simp only [normalized_primitive_local_cubic_count_eq h3]
  exact tendsto_const_nhds

/-- For a unit target every solution is primitive. -/
def unitTargetPrimitiveCubicSolutionsEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) {a : R} (ha : IsUnit a) :
    LocalCubicSolutions R I s a ≃ PrimitiveLocalCubicSolutions R I hI s a where
  toFun x := ⟨x.val, x.property, by
    by_contra h
    push_neg at h
    have he : residue R a = 0 := by
      calc
        residue R a = localResidueReduction I hI (Ideal.Quotient.mk I a) := rfl
        _ = localResidueReduction I hI (∑ i, x.val i ^ 3) := congrArg _ x.property.symm
        _ = 0 := by simp only [map_sum, map_pow, h, zero_pow (by decide : 3 ≠ 0),
          Finset.sum_const_zero]
    exact ((residue_ne_zero_iff_isUnit a).mpr ha) he⟩
  invFun x := ⟨x.val, x.property.1⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem unit_target_local_cubic_count_exact
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s n : ℕ) {a : R} (ha : IsUnit a) :
    localCubicSolutionCount R (maximalIdeal R ^ (n + 1)) (s + 1) a =
      Nat.card (PrimitiveCubicResidues R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * n) := by
  unfold localCubicSolutionCount
  rw [Nat.card_congr (unitTargetPrimitiveCubicSolutionsEquiv _
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) _ ha)]
  exact primitive_local_cubic_count_exact h3 s n a

theorem normalized_unit_target_local_cubic_count_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s n : ℕ) {a : R} (ha : IsUnit a) :
    normalizedLocalCubicCount R (s + 1) (n + 1) a =
      (Nat.card (PrimitiveCubicResidues R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s := by
  have he : normalizedLocalCubicCount R (s + 1) (n + 1) a =
      normalizedPrimitiveLocalCubicCount R (s + 1) n a := by
    unfold normalizedLocalCubicCount normalizedPrimitiveLocalCubicCount
    unfold localCubicSolutionCount primitiveLocalCubicSolutionCount
    rw [Nat.card_congr (unitTargetPrimitiveCubicSolutionsEquiv _
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) _ ha)]
  rw [he, normalized_primitive_local_cubic_count_eq h3]

/-- Genuine convergence of the full local density at primes avoiding `3a`. -/
theorem normalized_unit_target_local_cubic_count_tendsto
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s : ℕ) {a : R} (ha : IsUnit a) :
    Filter.Tendsto (fun e => normalizedLocalCubicCount R (s + 1) e a)
      Filter.atTop (nhds ((Nat.card (PrimitiveCubicResidues R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s)) := by
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun e he => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le he
  simpa only [Nat.add_comm 1 n] using
    (normalized_unit_target_local_cubic_count_eq h3 s n ha).symm

end WaringSiegel

#print axioms WaringSiegel.primitive_local_cubic_count_exact
