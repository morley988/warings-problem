import WaringSiegel.WSL3MomentLocalPowerLift
import WaringSiegel.WSL3MomentLocalPowerCount

/-! # Exact nonsingular power fibers for every positive degree -/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3
variable (k : ℕ)

theorem power_sub_mem_iff_of_same_residue
    {R : Type*} [CommRing R] [IsLocalRing R] (hk : 0<k) (hku : IsUnit (k:R))
    {x y : R} (hx : IsUnit x) (hxy : residue R x=residue R y) (I : Ideal R) :
    x^k-y^k∈I ↔ x-y∈I := by
  let B : R := ∑ j∈Finset.range k,x^j*y^(k-1-j)
  have hres : residue R B=(k:ResidueField R)*(residue R x)^(k-1) := by
    calc
      _=∑ j∈Finset.range k,(residue R x)^(k-1) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul,map_pow,← hxy]
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.mp hj
        omega
      _=_ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hB : IsUnit B := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [hres]
    exact mul_ne_zero (by simpa only [map_natCast] using (hku.map (residue R)).ne_zero)
      (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).mpr hx))
  have he : x^k-y^k=B*(x-y) := (geom_sum₂_mul x y k).symm
  rw [he,I.unit_mul_mem_iff_mem hB]

theorem power_root_unique_mod_ideal
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (hk : 0<k) (hku : IsUnit (k:R)) (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {a : R} {α : ResidueField R} (ha : α ^ k = residue R a) (hα : α ≠ 0) :
    ∃! z : R ⧸ I, z ^ k = Ideal.Quotient.mk I a ∧
      localResidueReduction I hI z = α := by
  obtain ⟨x, hx, hxr, hxu⟩ := power_lift_of_nonzero_residue k hk hku ha hα
  refine ⟨Ideal.Quotient.mk I x, ⟨by rw [← map_pow, hx], hxr⟩, ?_⟩
  intro z hz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq.mpr
  have hr : residue R x = residue R y := hxr.trans hz.2.symm
  have hc : x ^ k - y ^ k ∈ I := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_pow, hx] using hz.1.symm
  simpa only [neg_sub] using I.neg_mem
    ((power_sub_mem_iff_of_same_residue k hk hku hxu hr I).mp hc)

theorem power_eq_iff_of_same_nonzero_residue
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hk : 0<k) (hku : IsUnit (k:R)) (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {x y : R ⧸ I} (hxy : localResidueReduction I hI x = localResidueReduction I hI y)
    (hx : localResidueReduction I hI x ≠ 0) : x ^ k = y ^ k ↔ x = y := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq]
  exact power_sub_mem_iff_of_same_residue k hk hku
    ((residue_ne_zero_iff_isUnit u).mp hx) hxy I

def LocalPowerResidueClass
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) (α : Fin s → ResidueField R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ k) = Ideal.Quotient.mk I a ∧
    ∀ i, localResidueReduction I hI (x i) = α i}

def localPowerResidueClassTail
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) {s : ℕ} (a : R) (α : Fin (s + 1) → ResidueField R) :
    LocalPowerResidueClass k R I hI (s + 1) a α →
      (∀ i : Fin s, {z : R ⧸ I // localResidueReduction I hI z = α i.succ}) :=
  fun x i => ⟨x.val i.succ, x.property.2 i.succ⟩

/-- All coordinates except one are free once a nonsingular residue class is fixed. -/
theorem localPowerResidueClassTail_bijective
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (hk : 0<k) (hku : IsUnit (k:R)) (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {s : ℕ} (a : R) (α : Fin (s + 1) → ResidueField R)
    (ha : (∑ i, α i ^ k) = residue R a) (hα : α 0 ≠ 0) :
    Function.Bijective (localPowerResidueClassTail k I hI a α) := by
  classical
  constructor
  · intro x y h
    have ht : ∀ i : Fin s, x.val i.succ = y.val i.succ :=
      fun i => congrArg Subtype.val (congrFun h i)
    have hc : x.val 0 ^ k = y.val 0 ^ k := by
      have hx := x.property.1
      have hy := y.property.1
      rw [Fin.sum_univ_succ] at hx hy
      simp only [ht] at hx
      exact add_right_cancel (hx.trans hy.symm)
    have h0 : x.val 0 = y.val 0 :=
      (power_eq_iff_of_same_nonzero_residue k hk hku I hI
        ((x.property.2 0).trans (y.property.2 0).symm)
        ((x.property.2 0) ▸ hα)).mp hc
    apply Subtype.ext
    funext i
    exact Fin.cases h0 ht i
  · intro b
    choose y hy using fun i => Ideal.Quotient.mk_surjective (b i).val
    let c : R := a - ∑ i, y i ^ k
    have hr : α 0 ^ k = residue R c := by
      have he : ∀ i : Fin s, residue R (y i) = α i.succ := by
        intro i
        calc
          residue R (y i) = localResidueReduction I hI (Ideal.Quotient.mk I (y i)) := rfl
          _ = localResidueReduction I hI (b i).val := congrArg _ (hy i)
          _ = α i.succ := (b i).property
      simp only [c, map_sub, map_sum, map_pow, he]
      rw [← ha, Fin.sum_univ_succ]
      abel
    obtain ⟨z, hz, -⟩ := power_root_unique_mod_ideal k hk hku I hI hr hα
    refine ⟨⟨Fin.cons z (fun i => (b i).val), ?_⟩, ?_⟩
    · constructor
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hz.1, c, map_sub, map_sum, map_pow, hy]
        abel
      · intro i
        exact Fin.cases hz.2 (fun j => (b j).property) i
    · funext i
      exact Subtype.ext rfl

/-- Exact number of solutions at precision `n+1` in a fixed nonsingular
residue class. The exponent is the number of free coordinates times `n`. -/
theorem localPowerResidueClass_card
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) {s : ℕ} (a : R)
    (α : Fin (s + 1) → ResidueField R)
    (ha : (∑ i, α i ^ k) = residue R a) (hα : α 0 ≠ 0) (n : ℕ) :
    Nat.card (LocalPowerResidueClass k R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α) =
      Nat.card (ResidueField R) ^ (s * n) := by
  rw [Nat.card_congr (Equiv.ofBijective _
    (localPowerResidueClassTail_bijective k hk hku _ _ a α ha hα)), Nat.card_pi]
  simp only [residue_reduction_fiber_card, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm n s]

/-- Reindexing coordinates preserves the solution fiber and its cardinality. -/
def localPowerResidueClassPermute
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) {s : ℕ} (a : R)
    (α : Fin s → ResidueField R) (e : Fin s ≃ Fin s) :
    LocalPowerResidueClass k R I hI s a α ≃
      LocalPowerResidueClass k R I hI s a (fun i => α (e i)) where
  toFun x := ⟨fun i => x.val (e i),
    by exact (Equiv.sum_comp e (fun i => x.val i ^ k)).trans x.property.1,
    fun i => x.property.2 (e i)⟩
  invFun x := ⟨fun i => x.val (e.symm i),
    by exact (Equiv.sum_comp e.symm (fun i => x.val i ^ k)).trans x.property.1,
    fun i => by simpa using x.property.2 (e.symm i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

theorem localPowerResidueClass_card_of_nonzero
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (hk : 0<k) (hku : IsUnit (k:R)) {s : ℕ} (a : R)
    (α : Fin (s + 1) → ResidueField R)
    (ha : (∑ i, α i ^ k) = residue R a) (hα : ∃ i, α i ≠ 0) (n : ℕ) :
    Nat.card (LocalPowerResidueClass k R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α) =
      Nat.card (ResidueField R) ^ (s * n) := by
  classical
  obtain ⟨j, hj⟩ := hα
  let e := Equiv.swap (0 : Fin (s + 1)) j
  rw [Nat.card_congr (localPowerResidueClassPermute k _ _ a α e)]
  apply localPowerResidueClass_card k hk hku
  · exact (Equiv.sum_comp e (fun i => α i ^ k)).trans ha
  · simpa [e] using hj


#print axioms power_root_unique_mod_ideal
#print axioms localPowerResidueClass_card_of_nonzero
end WaringSiegel.WSL3
