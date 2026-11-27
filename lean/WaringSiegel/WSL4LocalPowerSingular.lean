import WaringSiegel.WSL4LocalPowerScaling

/-! # Exact singular scaling for arbitrary positive powers

The degree is written `k+1` in the scaling lemmas. Dividing every coordinate
by a uniformizer removes exactly `k+1` digits from the equation and leaves
`k` free digits in each coordinate. The primitive/singular split itself
is stated for every exponent.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (k : ℕ)

def SingularLocalPowerSolutions
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ k) = Ideal.Quotient.mk I a ∧
    ∀ i, localResidueReduction I hI (x i) = 0}

instance singularLocalPowerSolutions_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    Finite (SingularLocalPowerSolutions k R I hI s a) := by
  unfold SingularLocalPowerSolutions
  infer_instance

theorem uniformizer_scaled_power_congruence_iff
    {π : R} (hπ : Irreducible π) (n s : ℕ) (b : R)
    (y : Fin s → R ⧸ maximalIdeal R ^ (n + k)) :
    (∑ i, uniformizerMulQuotient hπ (n + k) (y i) ^ (k+1)) =
        Ideal.Quotient.mk (maximalIdeal R ^ (n + k + 1)) (π ^ (k+1) * b) ↔
      (∑ i, (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_add_right n k)) (y i)) ^ (k+1)) =
          Ideal.Quotient.mk (maximalIdeal R ^ n) b := by
  classical
  choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
  have hy : y = fun i => Ideal.Quotient.mk _ (z i) := funext fun i => (hz i).symm
  rw [hy]
  simp only [uniformizerMulQuotient_mk, Ideal.Quotient.factor_mk, ← map_pow, ← map_sum]
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq]
  have he : (∑ i, (π * z i) ^ (k+1)) - π ^ (k+1) * b =
      π ^ (k+1) * ((∑ i, z i ^ (k+1)) - b) := by
    simp only [mul_pow, ← Finset.mul_sum]
    ring
  rw [he]
  simpa only [Nat.add_assoc] using uniformizer_power_cancel_mem hπ (k+1) n

def singularLocalPowerScaleEquiv
    {π : R} (hπ : Irreducible π) (n s : ℕ) (b : R) :
    SingularLocalPowerSolutions (k+1) R (maximalIdeal R ^ (n+k+1))
      (Ideal.pow_le_self (by omega)) s (π ^ (k+1) * b) ≃
        PowerCongruenceTuples (k+1) R n k s b where
  toFun x :=
    ⟨fun i => (uniformizerZeroResidueEquiv hπ (n+k)).symm ⟨x.val i, x.property.2 i⟩,
      (uniformizer_scaled_power_congruence_iff k hπ n s b _).mp (by
        have he (i : Fin s) : uniformizerMulQuotient hπ (n+k)
            ((uniformizerZeroResidueEquiv hπ (n+k)).symm ⟨x.val i, x.property.2 i⟩) =
              x.val i := congrArg Subtype.val
          ((uniformizerZeroResidueEquiv hπ (n+k)).apply_symm_apply _)
        simpa only [he] using x.property.1)⟩
  invFun y := ⟨fun i => uniformizerMulQuotient hπ (n+k) (y.val i),
    (uniformizer_scaled_power_congruence_iff k hπ n s b y.val).mpr y.property,
    fun i => uniformizerMulQuotient_residue_zero hπ (n+k) (y.val i)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((uniformizerZeroResidueEquiv hπ (n+k)).apply_symm_apply _)
  right_inv y := by
    apply Subtype.ext
    funext i
    exact (uniformizerZeroResidueEquiv hπ (n+k)).symm_apply_apply _

theorem singular_local_power_count_scaled [Finite (ResidueField R)]
    {π : R} (hπ : Irreducible π) (n s : ℕ) (b : R) :
    Nat.card (SingularLocalPowerSolutions (k+1) R (maximalIdeal R ^ (n+k+1))
      (Ideal.pow_le_self (by omega)) s (π ^ (k+1) * b)) =
      localPowerSolutionCount R (maximalIdeal R ^ n) (k+1) s b *
        Nat.card (ResidueField R) ^ (s*k) := by
  rw [Nat.card_congr (singularLocalPowerScaleEquiv k hπ n s b)]
  exact power_congruence_tuples_card (k+1) n k s b

def localPowerPrimitiveSingularEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) :
    LocalPowerSolutions R I k s a ≃
      PrimitiveLocalPowerSolutions k R I hI s a ⊕
        SingularLocalPowerSolutions k R I hI s a := by
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

theorem local_power_count_primitive_add_singular
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) [Finite (R ⧸ I)] (s : ℕ) (a : R) :
    localPowerSolutionCount R I k s a =
      primitiveLocalPowerSolutionCount k R I hI s a +
        Nat.card (SingularLocalPowerSolutions k R I hI s a) := by
  unfold localPowerSolutionCount primitiveLocalPowerSolutionCount
  rw [Nat.card_congr (localPowerPrimitiveSingularEquiv k I hI s a), Nat.card_sum]

theorem singular_power_target_mem_power_ideal
    (n s : ℕ) {a : R}
    (x : SingularLocalPowerSolutions (k+1) R (maximalIdeal R ^ (n+k+1))
      (Ideal.pow_le_self (by omega)) s a) : a ∈ maximalIdeal R ^ (k+1) := by
  classical
  choose y hy using fun i => Ideal.Quotient.mk_surjective (x.val i)
  have hym (i : Fin s) : y i ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    rw [← localResidueReduction_mk (maximalIdeal R ^ (n+k+1))
      (Ideal.pow_le_self (by omega : n+k+1 ≠ 0)), hy]
    exact x.property.2 i
  have hsum : (∑ i, y i ^ (k+1)) ∈ maximalIdeal R ^ (k+1) :=
    Ideal.sum_mem _ (fun i _ => Ideal.pow_mem_pow (hym i) (k+1))
  have hd : (∑ i, y i ^ (k+1)) - a ∈ maximalIdeal R ^ (n+k+1) := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_sum, map_pow, hy] using x.property.1
  have hdk : (∑ i, y i ^ (k+1)) - a ∈ maximalIdeal R ^ (k+1) :=
    Ideal.pow_le_pow_right (by omega) hd
  have ha := (maximalIdeal R ^ (k+1)).sub_mem hsum hdk
  simpa only [sub_sub_cancel] using ha

theorem singular_local_power_count_zero
    (n s : ℕ) {a : R} (ha : a ∉ maximalIdeal R ^ (k+1)) :
    Nat.card (SingularLocalPowerSolutions (k+1) R (maximalIdeal R ^ (n+k+1))
      (Ideal.pow_le_self (by omega)) s a) = 0 := by
  letI : IsEmpty (SingularLocalPowerSolutions (k+1) R (maximalIdeal R ^ (n+k+1))
      (Ideal.pow_le_self (by omega)) s a) :=
    ⟨fun x => ha (singular_power_target_mem_power_ideal k n s x)⟩
  simp

#print axioms singular_local_power_count_scaled
#print axioms local_power_count_primitive_add_singular
#print axioms singular_local_power_count_zero
end WaringSiegel.WSL4Local
