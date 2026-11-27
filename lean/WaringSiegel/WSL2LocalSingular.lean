import WaringSiegel.WSL2LocalScaling

/-!
# Exact recursion for singular cubic solutions

At precision `n+3`, tuples with every coordinate in the maximal ideal are
scaled by a uniformizer and counted as lower-precision congruence tuples.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def SingularLocalCubicSolutions
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ 3) = Ideal.Quotient.mk I a ∧
    ∀ i, localResidueReduction I hI (x i) = 0}

instance singularLocalCubicSolutions_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    Finite (SingularLocalCubicSolutions R I hI s a) := by
  unfold SingularLocalCubicSolutions
  infer_instance

/-- Cubic congruence loses exactly three uniformizer digits under scaling. -/
theorem uniformizer_scaled_cubic_congruence_iff
    {π : R} (hπ : Irreducible π) (n s : ℕ) (b : R)
    (y : Fin s → R ⧸ maximalIdeal R ^ (n + 2)) :
    (∑ i, uniformizerMulQuotient hπ (n + 2) (y i) ^ 3) =
        Ideal.Quotient.mk (maximalIdeal R ^ (n + 3)) (π ^ 3 * b) ↔
      (∑ i, (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_add_right n 2)) (y i)) ^ 3) =
          Ideal.Quotient.mk (maximalIdeal R ^ n) b := by
  classical
  choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
  have hy : y = fun i => Ideal.Quotient.mk _ (z i) := funext fun i => (hz i).symm
  rw [hy]
  simp only [uniformizerMulQuotient_mk, Ideal.Quotient.factor_mk, ← map_pow, ← map_sum]
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]
  have he : (∑ i, (π * z i) ^ 3) - π ^ 3 * b =
      π ^ 3 * ((∑ i, z i ^ 3) - b) := by
    simp only [mul_pow, ← Finset.mul_sum]
    ring
  rw [he]
  exact uniformizer_power_cancel_mem hπ 3 n

/-- The singular quotient solutions are precisely lower congruence solutions
with two extra free digits in every scaled coordinate. -/
def singularLocalCubicScaleEquiv
    {π : R} (hπ : Irreducible π) (n s : ℕ) (b : R) :
    SingularLocalCubicSolutions R (maximalIdeal R ^ (n + 3))
      (Ideal.pow_le_self (by omega)) s (π ^ 3 * b) ≃
        CubicCongruenceTuples R n 2 s b where
  toFun x :=
    ⟨fun i => (uniformizerZeroResidueEquiv hπ (n + 2)).symm ⟨x.val i, x.property.2 i⟩,
      (uniformizer_scaled_cubic_congruence_iff hπ n s b _).mp (by
        have he (i : Fin s) : uniformizerMulQuotient hπ (n + 2)
            ((uniformizerZeroResidueEquiv hπ (n + 2)).symm ⟨x.val i, x.property.2 i⟩) =
              x.val i := congrArg Subtype.val
          ((uniformizerZeroResidueEquiv hπ (n + 2)).apply_symm_apply _)
        simpa only [he] using x.property.1)⟩
  invFun y := ⟨fun i => uniformizerMulQuotient hπ (n + 2) (y.val i),
    (uniformizer_scaled_cubic_congruence_iff hπ n s b y.val).mpr y.property,
    fun i => uniformizerMulQuotient_residue_zero hπ (n + 2) (y.val i)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((uniformizerZeroResidueEquiv hπ (n + 2)).apply_symm_apply _)
  right_inv y := by
    apply Subtype.ext
    funext i
    exact (uniformizerZeroResidueEquiv hπ (n + 2)).symm_apply_apply _

theorem singular_local_cubic_count_scaled [Finite (ResidueField R)]
    {π : R} (hπ : Irreducible π) (n s : ℕ) (b : R) :
    Nat.card (SingularLocalCubicSolutions R (maximalIdeal R ^ (n + 3))
      (Ideal.pow_le_self (by omega)) s (π ^ 3 * b)) =
      localCubicSolutionCount R (maximalIdeal R ^ n) s b *
        Nat.card (ResidueField R) ^ (s * 2) := by
  rw [Nat.card_congr (singularLocalCubicScaleEquiv hπ n s b)]
  exact cubic_congruence_tuples_card n 2 s b

/-- Literal solution tuples split disjointly into primitive and singular ones. -/
def localCubicPrimitiveSingularEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :
    LocalCubicSolutions R I s a ≃
      PrimitiveLocalCubicSolutions R I hI s a ⊕ SingularLocalCubicSolutions R I hI s a := by
  classical
  exact {
    toFun := fun x => if h : ∃ i, localResidueReduction I hI (x.val i) ≠ 0 then
      Sum.inl ⟨x.val, x.property, h⟩ else
      Sum.inr ⟨x.val, x.property, by simpa only [not_exists, not_not] using h⟩
    invFun := Sum.elim (fun x => ⟨x.val, x.property.1⟩) (fun x => ⟨x.val, x.property.1⟩)
    left_inv := fun x => by dsimp; split_ifs <;> rfl
    right_inv := fun x => by
      rcases x with x | x
      · simp only [dif_pos x.property.2, Sum.elim_inl]
        rfl
      · have h : ¬ ∃ i, localResidueReduction I hI (x.val i) ≠ 0 := by
          rintro ⟨i, hi⟩
          exact hi (x.property.2 i)
        simp only [dif_neg h, Sum.elim_inr]
        rfl }

theorem local_cubic_count_primitive_add_singular
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    localCubicSolutionCount R I s a =
      primitiveLocalCubicSolutionCount R I hI s a +
        Nat.card (SingularLocalCubicSolutions R I hI s a) := by
  unfold localCubicSolutionCount primitiveLocalCubicSolutionCount
  rw [Nat.card_congr (localCubicPrimitiveSingularEquiv I hI s a), Nat.card_sum]

theorem singular_cubic_target_mem_cube_ideal
    (n s : ℕ) {a : R}
    (x : SingularLocalCubicSolutions R (maximalIdeal R ^ (n + 3))
      (Ideal.pow_le_self (by omega)) s a) : a ∈ maximalIdeal R ^ 3 := by
  classical
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x.val i)
  have hym (i : Fin s) : y i ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    rw [← localResidueReduction_mk (maximalIdeal R ^ (n + 3))
      (Ideal.pow_le_self (by omega : n + 3 ≠ 0)), hy]
    exact x.property.2 i
  have hsum : (∑ i, y i ^ 3) ∈ maximalIdeal R ^ 3 :=
    Ideal.sum_mem _ (fun i _ => Ideal.pow_mem_pow (hym i) 3)
  have hd : (∑ i, y i ^ 3) - a ∈ maximalIdeal R ^ (n + 3) := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_sum, map_pow, hy] using x.property.1
  have hd3 : (∑ i, y i ^ 3) - a ∈ maximalIdeal R ^ 3 :=
    Ideal.pow_le_pow_right (by omega) hd
  have ha := (maximalIdeal R ^ 3).sub_mem hsum hd3
  simpa only [sub_sub_cancel] using ha

theorem singular_local_cubic_count_zero
    (n s : ℕ) {a : R} (ha : a ∉ maximalIdeal R ^ 3) :
    Nat.card (SingularLocalCubicSolutions R (maximalIdeal R ^ (n + 3))
      (Ideal.pow_le_self (by omega)) s a) = 0 := by
  letI : IsEmpty (SingularLocalCubicSolutions R (maximalIdeal R ^ (n + 3))
      (Ideal.pow_le_self (by omega)) s a) :=
    ⟨fun x => ha (singular_cubic_target_mem_cube_ideal n s x)⟩
  simp

end WaringSiegel

#print axioms WaringSiegel.singular_local_cubic_count_scaled
