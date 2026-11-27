import WaringSiegel.WSL2LocalDensity

/-!
# Exact nonsingular cubic fibers away from 3

When 3 is a unit, a prescribed nonzero residue root has exactly one lift at
any ideal precision. This yields exact counts in every nonsingular residue
class, strengthening the all-prime lower bounds.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

theorem cube_sub_mem_iff_of_same_residue
    {R : Type*} [CommRing R] [IsLocalRing R] (h3 : IsUnit (3 : R))
    {x y : R} (hx : IsUnit x) (hxy : residue R x = residue R y) (I : Ideal R) :
    x ^ 3 - y ^ 3 ∈ I ↔ x - y ∈ I := by
  have hB : IsUnit (x ^ 2 + x * y + y ^ 2) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have h3r := (h3.map (residue R)).ne_zero
    have hxr := (residue_ne_zero_iff_isUnit x).mpr hx
    have he : residue R (x ^ 2 + x * y + y ^ 2) =
        (3 : ResidueField R) * residue R x ^ 2 := by
      simp only [map_add, map_mul, map_pow, ← hxy]
      ring
    rw [he]
    exact mul_ne_zero (by simpa only [map_ofNat] using h3r) (pow_ne_zero _ hxr)
  have he : x ^ 3 - y ^ 3 = (x ^ 2 + x * y + y ^ 2) * (x - y) := by ring
  rw [he, I.unit_mul_mem_iff_mem hB]

def localResidueReduction
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) : R ⧸ I →+* ResidueField R :=
  Ideal.Quotient.factor hI

@[simp] theorem localResidueReduction_mk
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (x : R) :
    localResidueReduction I hI (Ideal.Quotient.mk I x) = residue R x := rfl

/-- A nonzero residue root determines exactly one root at any ideal precision. -/
theorem cube_root_unique_mod_ideal
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (h3 : IsUnit (3 : R)) (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {a : R} {α : ResidueField R} (ha : α ^ 3 = residue R a) (hα : α ≠ 0) :
    ∃! z : R ⧸ I, z ^ 3 = Ideal.Quotient.mk I a ∧
      localResidueReduction I hI z = α := by
  obtain ⟨x, hx, hxr, hxu⟩ := cube_lift_of_nonzero_residue h3 ha hα
  refine ⟨Ideal.Quotient.mk I x, ⟨by rw [← map_pow, hx], hxr⟩, ?_⟩
  intro z hz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq.mpr
  have hr : residue R x = residue R y := hxr.trans hz.2.symm
  have hc : x ^ 3 - y ^ 3 ∈ I := by
    apply Ideal.Quotient.eq.mp
    simpa only [map_pow, hx] using hz.1.symm
  simpa only [neg_sub] using I.neg_mem
    ((cube_sub_mem_iff_of_same_residue h3 hxu hr I).mp hc)

theorem cube_eq_iff_of_same_nonzero_residue
    {R : Type*} [CommRing R] [IsLocalRing R]
    (h3 : IsUnit (3 : R)) (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {x y : R ⧸ I} (hxy : localResidueReduction I hI x = localResidueReduction I hI y)
    (hx : localResidueReduction I hI x ≠ 0) : x ^ 3 = y ^ 3 ↔ x = y := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq]
  exact cube_sub_mem_iff_of_same_residue h3
    ((residue_ne_zero_iff_isUnit u).mp hx) hxy I

def LocalCubicResidueClass
    (R : Type*) [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) (s : ℕ) (a : R) (α : Fin s → ResidueField R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ 3) = Ideal.Quotient.mk I a ∧
    ∀ i, localResidueReduction I hI (x i) = α i}

def localCubicResidueClassTail
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) {s : ℕ} (a : R) (α : Fin (s + 1) → ResidueField R) :
    LocalCubicResidueClass R I hI (s + 1) a α →
      (∀ i : Fin s, {z : R ⧸ I // localResidueReduction I hI z = α i.succ}) :=
  fun x i => ⟨x.val i.succ, x.property.2 i.succ⟩

/-- All coordinates except one are free once a nonsingular residue class is fixed. -/
theorem localCubicResidueClassTail_bijective
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (h3 : IsUnit (3 : R)) (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {s : ℕ} (a : R) (α : Fin (s + 1) → ResidueField R)
    (ha : (∑ i, α i ^ 3) = residue R a) (hα : α 0 ≠ 0) :
    Function.Bijective (localCubicResidueClassTail I hI a α) := by
  classical
  constructor
  · intro x y h
    have ht : ∀ i : Fin s, x.val i.succ = y.val i.succ :=
      fun i => congrArg Subtype.val (congrFun h i)
    have hc : x.val 0 ^ 3 = y.val 0 ^ 3 := by
      have hx := x.property.1
      have hy := y.property.1
      rw [Fin.sum_univ_succ] at hx hy
      simp only [ht] at hx
      exact add_right_cancel (hx.trans hy.symm)
    have h0 : x.val 0 = y.val 0 :=
      (cube_eq_iff_of_same_nonzero_residue h3 I hI
        ((x.property.2 0).trans (y.property.2 0).symm)
        ((x.property.2 0) ▸ hα)).mp hc
    apply Subtype.ext
    funext i
    exact Fin.cases h0 ht i
  · intro b
    choose y hy using fun i => Ideal.Quotient.mk_surjective (b i).val
    let c : R := a - ∑ i, y i ^ 3
    have hr : α 0 ^ 3 = residue R c := by
      have he : ∀ i : Fin s, residue R (y i) = α i.succ := by
        intro i
        calc
          residue R (y i) = localResidueReduction I hI (Ideal.Quotient.mk I (y i)) := rfl
          _ = localResidueReduction I hI (b i).val := congrArg _ (hy i)
          _ = α i.succ := (b i).property
      simp only [c, map_sub, map_sum, map_pow, he]
      rw [← ha, Fin.sum_univ_succ]
      abel
    obtain ⟨z, hz, -⟩ := cube_root_unique_mod_ideal h3 I hI hr hα
    refine ⟨⟨Fin.cons z (fun i => (b i).val), ?_⟩, ?_⟩
    · constructor
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hz.1, c, map_sub, map_sum, map_pow, hy]
        abel
      · intro i
        exact Fin.cases hz.2 (fun j => (b j).property) i
    · funext i
      exact Subtype.ext rfl

theorem residue_reduction_fiber_card
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (ResidueField R)] (n : ℕ) (α : ResidueField R) :
    Nat.card {z : R ⧸ maximalIdeal R ^ (n + 1) //
      localResidueReduction _ (Ideal.pow_le_self (Nat.succ_ne_zero n)) z = α} =
      Nat.card (ResidueField R) ^ n := by
  let f := (localResidueReduction (maximalIdeal R ^ (n + 1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n))).toAddMonoidHom
  have hf : Function.Surjective f :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_self (Nat.succ_ne_zero n))
  have he : Nat.card {z : R ⧸ maximalIdeal R ^ (n + 1) // f z = α} =
      Nat.card f.ker :=
    Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf α)
  change Nat.card {z : R ⧸ maximalIdeal R ^ (n + 1) // f z = α} = _
  rw [he]
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ResidueField R))
  have hk := f.ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    AddSubgroup.card_top, dvr_power_quotient_card] at hk
  exact hk.trans (pow_succ (Nat.card (ResidueField R)) n)

/-- Exact number of solutions at precision `n+1` in a fixed nonsingular
residue class. The exponent is the number of free coordinates times `n`. -/
theorem localCubicResidueClass_card
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) {s : ℕ} (a : R)
    (α : Fin (s + 1) → ResidueField R)
    (ha : (∑ i, α i ^ 3) = residue R a) (hα : α 0 ≠ 0) (n : ℕ) :
    Nat.card (LocalCubicResidueClass R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α) =
      Nat.card (ResidueField R) ^ (s * n) := by
  rw [Nat.card_congr (Equiv.ofBijective _
    (localCubicResidueClassTail_bijective h3 _ _ a α ha hα)), Nat.card_pi]
  simp only [residue_reduction_fiber_card, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm n s]

/-- Reindexing coordinates preserves the solution fiber and its cardinality. -/
def localCubicResidueClassPermute
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ maximalIdeal R) {s : ℕ} (a : R)
    (α : Fin s → ResidueField R) (e : Fin s ≃ Fin s) :
    LocalCubicResidueClass R I hI s a α ≃
      LocalCubicResidueClass R I hI s a (fun i => α (e i)) where
  toFun x := ⟨fun i => x.val (e i),
    by exact (Equiv.sum_comp e (fun i => x.val i ^ 3)).trans x.property.1,
    fun i => x.property.2 (e i)⟩
  invFun x := ⟨fun i => x.val (e.symm i),
    by exact (Equiv.sum_comp e.symm (fun i => x.val i ^ 3)).trans x.property.1,
    fun i => by simpa using x.property.2 (e.symm i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

theorem localCubicResidueClass_card_of_nonzero
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : IsUnit (3 : R)) {s : ℕ} (a : R)
    (α : Fin (s + 1) → ResidueField R)
    (ha : (∑ i, α i ^ 3) = residue R a) (hα : ∃ i, α i ≠ 0) (n : ℕ) :
    Nat.card (LocalCubicResidueClass R (maximalIdeal R ^ (n + 1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) (s + 1) a α) =
      Nat.card (ResidueField R) ^ (s * n) := by
  classical
  obtain ⟨j, hj⟩ := hα
  let e := Equiv.swap (0 : Fin (s + 1)) j
  rw [Nat.card_congr (localCubicResidueClassPermute _ _ a α e)]
  apply localCubicResidueClass_card h3
  · exact (Equiv.sum_comp e (fun i => α i ^ 3)).trans ha
  · simpa [e] using hj

end WaringSiegel

#print axioms WaringSiegel.cube_root_unique_mod_ideal
#print axioms WaringSiegel.localCubicResidueClass_card
