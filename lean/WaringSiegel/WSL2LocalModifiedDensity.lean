import WaringSiegel.WSL2LocalFourUnit
import WaringSiegel.WSL2LocalOriginalDensity

/-!
# Exact restricted cubic local densities

At a prime containing the auxiliary coefficient p, the first four variables
occur as (p y)^3, and the last four are units. Every residue solution has
seven free lifting coordinates. The normalized density is exactly the
four-unit finite-field count divided by q^3, at every positive precision.
-/

noncomputable section
set_option maxHeartbeats 0
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical

namespace WaringSiegel

/-- In a quotient below the maximal ideal, a nonzero residue coordinate is
exactly a unit coordinate. -/
theorem localResidueReduction_ne_zero_iff_isUnit
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (x : R ⧸ I) :
    localResidueReduction I hI x ≠ 0 ↔ IsUnit x := by
  constructor
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    intro hr
    have hr' : residue R r ≠ 0 := hr
    exact ((residue_ne_zero_iff_isUnit r).mp hr').map (Ideal.Quotient.mk I)
  · intro hx
    exact (hx.map (localResidueReduction I hI)).ne_zero

def AllUnitCubicResidues
    (R : Type*) [CommRing R] [IsLocalRing R] (s : ℕ) (a : R) :=
  {α : Fin s → ResidueField R // (∑ i, α i ^ 3) = residue R a ∧ ∀ i, α i ≠ 0}

def AllUnitLocalCubicSolutions
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ 3) = Ideal.Quotient.mk I a ∧
    ∀ i, localResidueReduction I hI (x i) ≠ 0}

instance allUnitCubicResidues_finite
    {R : Type*} [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]
    (s : ℕ) (a : R) : Finite (AllUnitCubicResidues R s a) := by
  unfold AllUnitCubicResidues
  infer_instance

instance allUnitLocalCubicSolutions_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    Finite (AllUnitLocalCubicSolutions R I hI s a) := by
  unfold AllUnitLocalCubicSolutions
  infer_instance

def allUnitLocalCubicSolutionsEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :
    AllUnitLocalCubicSolutions R I hI s a ≃
      (Σ α : AllUnitCubicResidues R s a, LocalCubicResidueClass R I hI s a α.val) where
  toFun x :=
    ⟨⟨fun i => localResidueReduction I hI (x.val i), by
        simpa only [map_sum, map_pow, localResidueReduction_mk] using
          congrArg (localResidueReduction I hI) x.property.1, x.property.2⟩,
      ⟨x.val, x.property.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.val, x.2.property.1,
    fun i => (x.2.property.2 i) ▸ x.1.property.2 i⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by
    rcases x with ⟨⟨α, hα⟩, ⟨x, hx⟩⟩
    have he : (fun i => localResidueReduction I hI (x i)) = α := funext hx.2
    subst α
    rfl

/-- Exact lifting count with every coordinate a unit. -/
theorem all_unit_local_cubic_count_exact
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) (s n : ℕ) (a : R) :
    Nat.card (AllUnitLocalCubicSolutions R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a) =
      Nat.card (AllUnitCubicResidues R (s + 1) a) *
        Nat.card (ResidueField R) ^ (s * n) := by
  letI := dvr_power_quotient_finite (R := R) (n + 1)
  letI := Fintype.ofFinite (AllUnitCubicResidues R (s + 1) a)
  rw [Nat.card_congr (allUnitLocalCubicSolutionsEquiv _ _ _ _), Nat.card_sigma]
  have hc (α : AllUnitCubicResidues R (s + 1) a) :
      Nat.card (LocalCubicResidueClass R (maximalIdeal R ^ (n + 1))
        (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α.val) =
        Nat.card (ResidueField R) ^ (s * n) :=
    localCubicResidueClass_card h3 a α.val α.property.1 (α.property.2 0) n
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.cast_id]

theorem all_unit_residue_four_count_eq
    {R : Type*} [CommRing R] [IsLocalRing R] (a : R) :
    Nat.card (AllUnitCubicResidues R 4 a) =
      finiteFieldFourUnitCubicCount (ResidueField R) (residue R a) := by
  unfold finiteFieldFourUnitCubicCount
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨fun i => Units.mk0 (x.val i) (x.property.2 i), x.property.1⟩
      invFun := fun x => ⟨fun i => (x.val i : ResidueField R), x.property,
        fun i => Units.ne_zero (x.val i)⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; funext i; apply Units.ext; rfl }

/-- Literal restricted tuple solutions at a positive local precision. -/
def ModifiedLocalCubicSolutions
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (p a : R) :=
  {z : (Fin 4 → R ⧸ I) × (Fin 4 → R ⧸ I) //
    (∑ i, z.2 i ^ 3) + (∑ i, (Ideal.Quotient.mk I p * z.1 i) ^ 3) =
      Ideal.Quotient.mk I a ∧ ∀ i, localResidueReduction I hI (z.2 i) ≠ 0}

def modifiedCubicTarget
    {R : Type*} [CommRing R] (I : Ideal R) (p a : R) (y : Fin 4 → R ⧸ I) : R :=
  a - ∑ i, (p * Quotient.out (y i)) ^ 3

theorem modifiedCubicTarget_mk
    {R : Type*} [CommRing R] (I : Ideal R) (p a : R) (y : Fin 4 → R ⧸ I) :
    Ideal.Quotient.mk I (modifiedCubicTarget I p a y) =
      Ideal.Quotient.mk I a - ∑ i, (Ideal.Quotient.mk I p * y i) ^ 3 := by
  simp only [modifiedCubicTarget, map_sub, map_sum, map_pow, map_mul, Ideal.Quotient.mk_out]

theorem modifiedCubicTarget_residue
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    {p : R} (hp : p ∈ maximalIdeal R) (a : R) (y : Fin 4 → R ⧸ I) :
    residue R (modifiedCubicTarget I p a y) = residue R a := by
  have hp0 : residue R p = 0 := (residue_eq_zero_iff p).mpr hp
  simp only [modifiedCubicTarget, map_sub, map_sum, map_pow, map_mul, hp0,
    zero_mul, zero_pow (by decide : 3 ≠ 0), Finset.sum_const_zero, sub_zero]

def modifiedLocalCubicSolutionsEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (p a : R) :
    ModifiedLocalCubicSolutions R I hI p a ≃
      (Σ y : Fin 4 → R ⧸ I, AllUnitLocalCubicSolutions R I hI 4
        (modifiedCubicTarget I p a y)) where
  toFun z := ⟨z.val.1, ⟨z.val.2, by
    rw [modifiedCubicTarget_mk]
    exact (eq_sub_iff_add_eq).mpr z.property.1, z.property.2⟩⟩
  invFun z := ⟨(z.1, z.2.val), by
    have h := z.2.property.1.trans (modifiedCubicTarget_mk I p a z.1)
    exact ⟨eq_sub_iff_add_eq.mp h, z.2.property.2⟩⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := rfl

/-- Every residue four-unit solution contributes precisely seven free digits
at each further precision; the four p-divisible variables remain free. -/
theorem modified_local_cubic_count_exact
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) {p : R} (hp : p ∈ maximalIdeal R) (a : R) (n : ℕ) :
    Nat.card (ModifiedLocalCubicSolutions R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) p a) =
      finiteFieldFourUnitCubicCount (ResidueField R) (residue R a) *
        Nat.card (ResidueField R) ^ (7 * n + 4) := by
  letI := dvr_power_quotient_finite (R := R) (n + 1)
  letI := Fintype.ofFinite (R ⧸ maximalIdeal R ^ (n + 1))
  rw [Nat.card_congr (modifiedLocalCubicSolutionsEquiv _ _ _ _), Nat.card_sigma]
  have hc (y : Fin 4 → R ⧸ maximalIdeal R ^ (n + 1)) :
      Nat.card (AllUnitLocalCubicSolutions R (maximalIdeal R ^ (n + 1))
        (Ideal.pow_le_self (Nat.succ_ne_zero n)) 4
          (modifiedCubicTarget _ p a y)) =
        finiteFieldFourUnitCubicCount (ResidueField R) (residue R a) *
          Nat.card (ResidueField R) ^ (3 * n) := by
    rw [all_unit_local_cubic_count_exact h3 3 n,
      all_unit_residue_four_count_eq, modifiedCubicTarget_residue _ hp]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, Nat.cast_id, Nat.card_fun, Nat.card_fin, dvr_power_quotient_card]
  rw [mul_left_comm, ← pow_mul, ← pow_add]
  congr 2
  omega

def normalizedModifiedLocalCubicCount
    (R : Type*) [CommRing R] [IsLocalRing R] (p a : R) (n : ℕ) : ℝ :=
  (Nat.card (ModifiedLocalCubicSolutions R (maximalIdeal R ^ (n + 1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) p a) : ℝ) /
      (Nat.card (ResidueField R) : ℝ) ^ (7 * (n + 1))

/-- The modified local density is exactly constant at every positive precision. -/
theorem normalized_modified_local_cubic_count_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) {p : R} (hp : p ∈ maximalIdeal R) (a : R) (n : ℕ) :
    normalizedModifiedLocalCubicCount R p a n =
      (finiteFieldFourUnitCubicCount (ResidueField R) (residue R a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ 3 := by
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ResidueField R)).ne'
  unfold normalizedModifiedLocalCubicCount
  rw [modified_local_cubic_count_exact h3 hp, Nat.cast_mul, Nat.cast_pow]
  have he : 7 * (n + 1) = (7 * n + 4) + 3 := by omega
  rw [he, pow_add]
  field_simp
  simp only [pow_add]
  ring

/-- Quantitative positivity for the actual restricted local solution count. -/
theorem normalized_modified_local_cubic_count_lower
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h6 : (6 : ResidueField R) ≠ 0) {p : R} (hp : p ∈ maximalIdeal R)
    (hq : 24576 ≤ Nat.card (ResidueField R)) (a : R) (n : ℕ) :
    (1 / 2 : ℝ) ≤ normalizedModifiedLocalCubicCount R p a n := by
  letI := Fintype.ofFinite (ResidueField R)
  rw [normalized_modified_local_cubic_count_eq
    (three_isUnit_of_six_residue_ne_zero h6) hp]
  simpa only [Nat.card_eq_fintype_card] using
    finite_field_four_unit_cubic_normalized_lower h6
      (by simpa only [Nat.card_eq_fintype_card] using hq) (residue R a)

theorem normalized_modified_local_cubic_count_tendsto
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) {p : R} (hp : p ∈ maximalIdeal R) (a : R) :
    Tendsto (normalizedModifiedLocalCubicCount R p a) atTop
      (𝓝 ((finiteFieldFourUnitCubicCount (ResidueField R) (residue R a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ 3)) := by
  have heq : normalizedModifiedLocalCubicCount R p a = fun _ : ℕ =>
      (finiteFieldFourUnitCubicCount (ResidueField R) (residue R a) : ℝ) /
        (Nat.card (ResidueField R) : ℝ) ^ 3 := by
    funext n
    exact normalized_modified_local_cubic_count_eq h3 hp a n
  rw [heq]
  exact tendsto_const_nhds

variable {K : Type*} [Field K] [NumberField K]

/-- The restricted local factor in an actual number-field completion is at
least one half, uniformly in every target, at the proved large-norm threshold. -/
theorem completion_modified_cubic_count_lower
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 24576 ≤ Ideal.absNorm v.asIdeal)
    {p : 𝓞 K} (hp : p ∈ v.asIdeal) (ν : 𝓞 K) (n : ℕ) :
    (1 / 2 : ℝ) ≤ normalizedModifiedLocalCubicCount (v.adicCompletionIntegers K)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) p)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) n := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  have h6' : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    fun h => h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hp' : algebraMap (𝓞 K) (v.adicCompletionIntegers K) p ∈
      maximalIdeal (v.adicCompletionIntegers K) := by
    simpa only [pow_one] using
      (completion_mem_maximalIdeal_pow_iff v p 1).mpr (by simpa only [pow_one] using hp)
  apply normalized_modified_local_cubic_count_lower h6' hp'
  simpa only [completion_residue_card_eq_absNorm] using hq

end WaringSiegel

#print axioms WaringSiegel.modified_local_cubic_count_exact

#print axioms WaringSiegel.normalized_modified_local_cubic_count_eq
#print axioms WaringSiegel.completion_modified_cubic_count_lower
