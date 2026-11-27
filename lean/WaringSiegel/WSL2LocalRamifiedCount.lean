import WaringSiegel.WSL2LocalRamified

/-!
# Exact counts in ramified cubic coordinate classes

A primitive solution class modulo `m^(v(3)+1)` has a fixed number of first
coordinate roots and free remaining coordinates. This supplies the finite
partition needed for local-density stabilization at primes over 3.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

def LocalCubicIdealClass
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    (s : ℕ) (a : R) (α : Fin s → R ⧸ maximalIdeal R ^ L) :=
  {x : Fin s → R ⧸ maximalIdeal R ^ e //
    (∑ i, x i ^ 3) = Ideal.Quotient.mk _ a ∧
      ∀ i, Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) (x i) = α i}

def CubicIdealTail
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L) :=
  ∀ i : Fin s, {z : R ⧸ maximalIdeal R ^ e //
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) z = α i.succ}

def CubicIdealHeadFiber
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (a : R) (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L)
    (b : CubicIdealTail R e L hLe α) :=
  {z : R ⧸ maximalIdeal R ^ e // z ^ 3 + (∑ i, (b i).val ^ 3) = Ideal.Quotient.mk _ a ∧
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) z = α 0}

def localCubicIdealClassEquiv
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (a : R) (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L) :
    LocalCubicIdealClass R e L hLe (s + 1) a α ≃
      (Σ b : CubicIdealTail R e L hLe α, CubicIdealHeadFiber R e L hLe a α b) where
  toFun x := ⟨fun i => ⟨x.val i.succ, x.property.2 i.succ⟩,
    ⟨x.val 0, by simpa only [Fin.sum_univ_succ] using x.property.1, x.property.2 0⟩⟩
  invFun x := ⟨Fin.cons x.2.val (fun i => (x.1 i).val),
    by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using x.2.property.1,
    fun i => Fin.cases x.2.property.2 (fun j => (x.1 j).property) i⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by
    rcases x with ⟨b, z⟩
    rfl

instance cubicIdealTail_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    [Finite (R ⧸ maximalIdeal R ^ e)] {s : ℕ}
    (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L) :
    Finite (CubicIdealTail R e L hLe α) := by
  unfold CubicIdealTail
  infer_instance

instance cubicIdealHeadFiber_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    [Finite (R ⧸ maximalIdeal R ^ e)] {s : ℕ}
    (a : R) (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L)
    (b : CubicIdealTail R e L hLe α) : Finite (CubicIdealHeadFiber R e L hLe a α b) := by
  unfold CubicIdealHeadFiber
  infer_instance

instance localCubicIdealClass_finite
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    [Finite (R ⧸ maximalIdeal R ^ e)] (s : ℕ)
    (a : R) (α : Fin s → R ⧸ maximalIdeal R ^ L) :
    Finite (LocalCubicIdealClass R e L hLe s a α) := by
  unfold LocalCubicIdealClass
  infer_instance

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

/-- The first-coordinate fiber has `q^v(3)` roots after every choice of tails. -/
theorem cubic_ideal_head_fiber_card
    (h3 : (3 : R) ≠ 0) {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0))
    (r : ℕ)
    (b : CubicIdealTail R ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (x i))) :
    Nat.card (CubicIdealHeadFiber R ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) (∑ i, x i ^ 3)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (x i)) b) =
        Nat.card (ResidueField R) ^ cubicDerivativeOrder R := by
  classical
  choose y hy using fun i => Ideal.Quotient.mk_surjective (b i).val
  let c : R := (∑ i, x i ^ 3) - ∑ i, y i ^ 3
  have hyb (i : Fin s) : y i - x i.succ ∈ cubicBranchIdeal R := by
    rw [cubicBranchIdeal_eq_power R h3]
    apply Ideal.Quotient.eq.mp
    have h := (b i).property
    rw [← hy i, Ideal.Quotient.factor_mk] at h
    exact h
  have hc : c - x 0 ^ 3 ∈ cubicStabilityIdeal R := by
    have he : c - x 0 ^ 3 = ∑ i : Fin s, (x i.succ ^ 3 - y i ^ 3) := by
      dsimp [c]
      rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
      ring
    rw [he]
    apply Ideal.sum_mem
    intro i _
    simpa only [neg_sub] using (cubicStabilityIdeal R).neg_mem
      (cube_sub_mem_stability_of_branch (hyb i))
  have he : CubicIdealHeadFiber R ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) (∑ i, x i ^ 3)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (x i)) b ≃
      CubicRootBranch R ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
        (cubicDerivativeOrder R + 1) (by omega) c (x 0) :=
    Equiv.subtypeEquivRight (by
      intro z
      simp only [c, map_sub, map_sum, map_pow, hy]
      exact and_congr_left (fun _ => eq_sub_iff_add_eq.symm))
  rw [Nat.card_congr he]
  exact cubic_root_branch_card h3 hx hc (cubicDerivativeOrder R + 1 + r) (by omega)

theorem local_cubic_ideal_class_card_of_unit_first
    (h3 : (3 : R) ≠ 0) {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0)) (r : ℕ) :
    Nat.card (LocalCubicIdealClass R ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) (s + 1) (∑ i, x i ^ 3)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (x i))) =
        Nat.card (ResidueField R) ^ (s * (r + cubicDerivativeOrder R) + cubicDerivativeOrder R) := by
  classical
  letI := dvr_power_quotient_finite (R := R)
    ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
  let α : Fin (s + 1) → R ⧸ maximalIdeal R ^ (cubicDerivativeOrder R + 1) :=
    fun i => Ideal.Quotient.mk _ (x i)
  letI := Fintype.ofFinite (CubicIdealTail R
    ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) α)
  rw [Nat.card_congr (localCubicIdealClassEquiv _ _ _ _ _), Nat.card_sigma]
  simp only [cubic_ideal_head_fiber_card h3 x hx r, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.cast_id]
  have hf (i : Fin s) : Nat.card {z : R ⧸ maximalIdeal R ^
      ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R) //
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega :
          cubicDerivativeOrder R + 1 ≤
            (cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)) z = α i.succ} =
      Nat.card (ResidueField R) ^ (r + cubicDerivativeOrder R) := by
    rw [dvr_reduction_fiber_card_of_le (cubicDerivativeOrder R + 1)
      ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R) (by omega)]
    congr 1
    omega
  change Nat.card (CubicIdealTail R _ _ _ α) * _ = _
  unfold CubicIdealTail
  simp only [Nat.card_pi, hf, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Nat.mul_comm (r + cubicDerivativeOrder R) s, ← pow_add]

def localCubicIdealClassPermute
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (a : R) (α : Fin s → R ⧸ maximalIdeal R ^ L) (p : Fin s ≃ Fin s) :
    LocalCubicIdealClass R e L hLe s a α ≃
      LocalCubicIdealClass R e L hLe s a (fun i => α (p i)) where
  toFun x := ⟨fun i => x.val (p i),
    (Equiv.sum_comp p (fun i => x.val i ^ 3)).trans x.property.1,
    fun i => x.property.2 (p i)⟩
  invFun x := ⟨fun i => x.val (p.symm i),
    (Equiv.sum_comp p.symm (fun i => x.val i ^ 3)).trans x.property.1,
    fun i => by simpa using x.property.2 (p.symm i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

theorem local_cubic_ideal_class_card_of_unit
    (h3 : (3 : R) ≠ 0) {s : ℕ} (x : Fin (s + 1) → R)
    (hx : ∃ i, IsUnit (x i)) (r : ℕ) :
    Nat.card (LocalCubicIdealClass R ((cubicDerivativeOrder R + 1 + r) + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) (s + 1) (∑ i, x i ^ 3)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (x i))) =
        Nat.card (ResidueField R) ^ (s * (r + cubicDerivativeOrder R) + cubicDerivativeOrder R) := by
  classical
  obtain ⟨j, hj⟩ := hx
  let p := Equiv.swap (0 : Fin (s + 1)) j
  have hsum := Equiv.sum_comp p (fun i => x i ^ 3)
  rw [Nat.card_congr (localCubicIdealClassPermute _ _ _ _ _ p)]
  rw [← hsum]
  exact local_cubic_ideal_class_card_of_unit_first h3 (fun i => x (p i)) (by simpa [p] using hj) r

end WaringSiegel

#print axioms WaringSiegel.cubic_ideal_head_fiber_card

#print axioms WaringSiegel.local_cubic_ideal_class_card_of_unit
