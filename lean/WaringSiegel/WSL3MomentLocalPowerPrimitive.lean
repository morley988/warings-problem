import WaringSiegel.WSL3MomentLocalPowerGood

/-! # Actual primitive local densities for every positive exponent -/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3
variable (k : ℕ)

def PrimitivePowerResidues
    (R : Type*) [CommRing R] [IsLocalRing R] (s : ℕ) (a : R) :=
  {α : Fin s → ResidueField R // (∑ i, α i ^ k) = residue R a ∧ ∃ i, α i ≠ 0}

def PrimitiveLocalPowerSolutions
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ k) = Ideal.Quotient.mk I a ∧
    ∃ i, localResidueReduction I hI (x i) ≠ 0}

def primitiveLocalPowerSolutionCount
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) : ℕ :=
  Nat.card (PrimitiveLocalPowerSolutions k R I hI s a)

instance primitivePowerResidues_finite
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    (s : ℕ) (a : R) : Finite (PrimitivePowerResidues k R s a) := by
  unfold PrimitivePowerResidues
  infer_instance

instance primitiveLocalPowerSolutions_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    Finite (PrimitiveLocalPowerSolutions k R I hI s a) := by
  unfold PrimitiveLocalPowerSolutions
  infer_instance

instance localPowerResidueClass_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R)
    (α : Fin s → ResidueField R) : Finite (LocalPowerResidueClass k R I hI s a α) := by
  unfold LocalPowerResidueClass
  infer_instance

/-- Partition actual primitive quotient tuples by their residue tuple. -/
def primitiveLocalPowerSolutionsEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :
    PrimitiveLocalPowerSolutions k R I hI s a ≃
      (Σ α : PrimitivePowerResidues k R s a, LocalPowerResidueClass k R I hI s a α.val) where
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
theorem primitive_local_power_count_exact
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) (s n : ℕ) (a : R) :
    primitiveLocalPowerSolutionCount k R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a =
      Nat.card (PrimitivePowerResidues k R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * n) := by
  classical
  letI := dvr_power_quotient_finite (R := R) (n + 1)
  letI := Fintype.ofFinite (PrimitivePowerResidues k R (s + 1) a)
  unfold primitiveLocalPowerSolutionCount
  rw [Nat.card_congr (primitiveLocalPowerSolutionsEquiv k _ _ _ _), Nat.card_sigma]
  have hc (α : PrimitivePowerResidues k R (s + 1) a) :
      Nat.card (LocalPowerResidueClass k R (maximalIdeal R ^ (n + 1))
        (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α.val) =
        Nat.card (ResidueField R) ^ (s * n) :=
    localPowerResidueClass_card_of_nonzero k hk hku a α.val α.property.1 α.property.2 n
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.cast_id]

def normalizedPrimitiveLocalPowerCount
    (R : Type*) [CommRing R] [IsLocalRing R] (s n : ℕ) (a : R) : ℝ :=
  (primitiveLocalPowerSolutionCount k R (maximalIdeal R ^ (n + 1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) s a : ℝ) /
      (Nat.card (ResidueField R) : ℝ) ^ ((s - 1) * (n + 1))

/-- The primitive normalized sequence is exactly constant when k is a unit. -/
theorem normalized_primitive_local_power_count_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) (s n : ℕ) (a : R) :
    normalizedPrimitiveLocalPowerCount k R (s + 1) n a =
      (Nat.card (PrimitivePowerResidues k R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ResidueField R)).ne'
  unfold normalizedPrimitiveLocalPowerCount
  rw [primitive_local_power_count_exact k hk hku]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.add_sub_cancel, Nat.mul_add,
    Nat.mul_one, pow_add]
  simpa only [mul_comm ((Nat.card (ResidueField R) : ℝ) ^ s)] using
    (mul_div_mul_right (Nat.card (PrimitivePowerResidues k R (s + 1) a) : ℝ)
      ((Nat.card (ResidueField R) : ℝ) ^ s) (pow_ne_zero (s * n) hq))

theorem normalized_primitive_local_power_count_tendsto
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) (s : ℕ) (a : R) :
    Filter.Tendsto (fun n => normalizedPrimitiveLocalPowerCount k R (s + 1) n a)
      Filter.atTop (nhds ((Nat.card (PrimitivePowerResidues k R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s)) := by
  simp only [normalized_primitive_local_power_count_eq k hk hku]
  exact tendsto_const_nhds

/-- For a unit target every solution is primitive. -/
def unitTargetPrimitivePowerSolutionsEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (hk : 0<k) (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) {a : R} (ha : IsUnit a) :
    LocalPowerSolutions R I k s a ≃ PrimitiveLocalPowerSolutions k R I hI s a where
  toFun x := ⟨x.val, x.property, by
    by_contra h
    push_neg at h
    have he : residue R a = 0 := by
      calc
        residue R a = localResidueReduction I hI (Ideal.Quotient.mk I a) := rfl
        _ = localResidueReduction I hI (∑ i, x.val i ^ k) := congrArg _ x.property.symm
        _ = 0 := by simp only [map_sum, map_pow, h, zero_pow hk.ne',
          Finset.sum_const_zero]
    exact ((residue_ne_zero_iff_isUnit a).mpr ha) he⟩
  invFun x := ⟨x.val, x.property.1⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem unit_target_local_power_count_exact
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) (s n : ℕ) {a : R} (ha : IsUnit a) :
    localPowerSolutionCount R (maximalIdeal R ^ (n + 1)) k (s + 1) a =
      Nat.card (PrimitivePowerResidues k R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * n) := by
  unfold localPowerSolutionCount
  rw [Nat.card_congr (unitTargetPrimitivePowerSolutionsEquiv k hk _
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) _ ha)]
  exact primitive_local_power_count_exact k hk hku s n a

theorem normalized_unit_target_local_power_count_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) (s n : ℕ) {a : R} (ha : IsUnit a) :
    normalizedLocalPowerCount R k (s + 1) (n + 1) a =
      (Nat.card (PrimitivePowerResidues k R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s := by
  have he : normalizedLocalPowerCount R k (s + 1) (n + 1) a =
      normalizedPrimitiveLocalPowerCount k R (s + 1) n a := by
    unfold normalizedLocalPowerCount normalizedPrimitiveLocalPowerCount
    unfold localPowerSolutionCount primitiveLocalPowerSolutionCount
    rw [Nat.card_congr (unitTargetPrimitivePowerSolutionsEquiv k hk _
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) _ ha)]
  rw [he, normalized_primitive_local_power_count_eq k hk hku]

/-- Genuine convergence of the full local density when k and the target are units. -/
theorem normalized_unit_target_local_power_count_tendsto
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) (s : ℕ) {a : R} (ha : IsUnit a) :
    Filter.Tendsto (fun e => normalizedLocalPowerCount R k (s + 1) e a)
      Filter.atTop (nhds ((Nat.card (PrimitivePowerResidues k R (s + 1) a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ s)) := by
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  apply Filter.eventually_atTop.mpr
  refine ⟨1, fun e he => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le he
  simpa only [Nat.add_comm 1 n] using
    (normalized_unit_target_local_power_count_eq k hk hku s n ha).symm


#print axioms primitive_local_power_count_exact
#print axioms normalized_primitive_local_power_count_tendsto
#print axioms normalized_unit_target_local_power_count_tendsto
end WaringSiegel.WSL3
