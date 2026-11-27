import WaringSiegel.WSL3MomentLocalPowerBranchLift

/-!
# Exact counts in ramified power coordinate classes

A primitive solution class modulo `m^(v(k)+1)` has a fixed number of first
coordinate roots and free remaining coordinates. This supplies the finite
partition needed for local-density stabilization at all finite primes.
-/

noncomputable section
set_option maxHeartbeats 1400000

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel.WSL3

def LocalPowerIdealClass (k : ℕ)
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    (s : ℕ) (a : R) (α : Fin s → R ⧸ maximalIdeal R ^ L) :=
  {x : Fin s → R ⧸ maximalIdeal R ^ e //
    (∑ i, x i ^ k) = Ideal.Quotient.mk _ a ∧
      ∀ i, Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) (x i) = α i}

def PowerIdealTail (k : ℕ)
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L) :=
  ∀ i : Fin s, {z : R ⧸ maximalIdeal R ^ e //
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) z = α i.succ}

def PowerIdealHeadFiber (k : ℕ)
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (a : R) (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L)
    (b : PowerIdealTail k R e L hLe α) :=
  {z : R ⧸ maximalIdeal R ^ e // z ^ k + (∑ i, (b i).val ^ k) = Ideal.Quotient.mk _ a ∧
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) z = α 0}

def localPowerIdealClassEquiv (k : ℕ)
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (a : R) (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L) :
    LocalPowerIdealClass k R e L hLe (s + 1) a α ≃
      (Σ b : PowerIdealTail k R e L hLe α, PowerIdealHeadFiber k R e L hLe a α b) where
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

instance powerIdealTail_finite (k : ℕ)
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    [Finite (R ⧸ maximalIdeal R ^ e)] {s : ℕ}
    (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L) :
    Finite (PowerIdealTail k R e L hLe α) := by
  unfold PowerIdealTail
  infer_instance

instance powerIdealHeadFiber_finite (k : ℕ)
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    [Finite (R ⧸ maximalIdeal R ^ e)] {s : ℕ}
    (a : R) (α : Fin (s + 1) → R ⧸ maximalIdeal R ^ L)
    (b : PowerIdealTail k R e L hLe α) : Finite (PowerIdealHeadFiber k R e L hLe a α b) := by
  unfold PowerIdealHeadFiber
  infer_instance

instance localPowerIdealClass_finite (k : ℕ)
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    [Finite (R ⧸ maximalIdeal R ^ e)] (s : ℕ)
    (a : R) (α : Fin s → R ⧸ maximalIdeal R ^ L) :
    Finite (LocalPowerIdealClass k R e L hLe s a α) := by
  unfold LocalPowerIdealClass
  infer_instance

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

/-- The first-coordinate fiber has `q^v(k)` roots after every choice of tails. -/
theorem power_ideal_head_fiber_card (k : ℕ)
    (hk : 0<k) (hk0 : (k : R) ≠ 0) {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0))
    (r : ℕ)
    (b : PowerIdealTail k R ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
      (powerDerivativeOrder R k + 1) (by omega)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (x i))) :
    Nat.card (PowerIdealHeadFiber k R ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
      (powerDerivativeOrder R k + 1) (by omega) (∑ i, x i ^ k)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (x i)) b) =
        Nat.card (ResidueField R) ^ powerDerivativeOrder R k := by
  classical
  choose y hy using fun i => Ideal.Quotient.mk_surjective (b i).val
  let c : R := (∑ i, x i ^ k) - ∑ i, y i ^ k
  have hyb (i : Fin s) : y i - x i.succ ∈ powerBranchIdeal R k := by
    rw [powerBranchIdeal_eq_power R k hk0]
    apply Ideal.Quotient.eq.mp
    have h := (b i).property
    rw [← hy i, Ideal.Quotient.factor_mk] at h
    exact h
  have hc : c - x 0 ^ k ∈ powerStabilityIdeal R k := by
    have he : c - x 0 ^ k = ∑ i : Fin s, (x i.succ ^ k - y i ^ k) := by
      dsimp [c]
      rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
      ring
    rw [he]
    apply Ideal.sum_mem
    intro i _
    simpa only [neg_sub] using (powerStabilityIdeal R k).neg_mem
      (power_sub_mem_stability_of_branch k (hyb i))
  have he : PowerIdealHeadFiber k R ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
      (powerDerivativeOrder R k + 1) (by omega) (∑ i, x i ^ k)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (x i)) b ≃
      PowerRootBranch R k ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
        (powerDerivativeOrder R k + 1) (by omega) c (x 0) :=
    Equiv.subtypeEquivRight (by
      intro z
      simp only [c, map_sub, map_sum, map_pow, hy]
      exact and_congr_left (fun _ => eq_sub_iff_add_eq.symm))
  rw [Nat.card_congr he]
  exact power_root_branch_card k hk hk0 hx hc (powerDerivativeOrder R k + 1 + r) (by omega)

theorem local_power_ideal_class_card_of_unit_first (k : ℕ)
    (hk : 0<k) (hk0 : (k : R) ≠ 0) {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0)) (r : ℕ) :
    Nat.card (LocalPowerIdealClass k R ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
      (powerDerivativeOrder R k + 1) (by omega) (s + 1) (∑ i, x i ^ k)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (x i))) =
        Nat.card (ResidueField R) ^ (s * (r + powerDerivativeOrder R k) + powerDerivativeOrder R k) := by
  classical
  letI := dvr_power_quotient_finite (R := R)
    ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
  let α : Fin (s + 1) → R ⧸ maximalIdeal R ^ (powerDerivativeOrder R k + 1) :=
    fun i => Ideal.Quotient.mk _ (x i)
  letI := Fintype.ofFinite (PowerIdealTail k R
    ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
      (powerDerivativeOrder R k + 1) (by omega) α)
  rw [Nat.card_congr (localPowerIdealClassEquiv k _ _ _ _ _), Nat.card_sigma]
  simp only [power_ideal_head_fiber_card k hk hk0 x hx r, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.cast_id]
  have hf (i : Fin s) : Nat.card {z : R ⧸ maximalIdeal R ^
      ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k) //
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega :
          powerDerivativeOrder R k + 1 ≤
            (powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)) z = α i.succ} =
      Nat.card (ResidueField R) ^ (r + powerDerivativeOrder R k) := by
    rw [dvr_reduction_fiber_card_of_le (powerDerivativeOrder R k + 1)
      ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k) (by omega)]
    congr 1
    omega
  change Nat.card (PowerIdealTail k R _ _ _ α) * _ = _
  unfold PowerIdealTail
  simp only [Nat.card_pi, hf, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Nat.mul_comm (r + powerDerivativeOrder R k) s, ← pow_add]

def localPowerIdealClassPermute (k : ℕ)
    {R : Type*} [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e)
    {s : ℕ} (a : R) (α : Fin s → R ⧸ maximalIdeal R ^ L) (p : Fin s ≃ Fin s) :
    LocalPowerIdealClass k R e L hLe s a α ≃
      LocalPowerIdealClass k R e L hLe s a (fun i => α (p i)) where
  toFun x := ⟨fun i => x.val (p i),
    (Equiv.sum_comp p (fun i => x.val i ^ k)).trans x.property.1,
    fun i => x.property.2 (p i)⟩
  invFun x := ⟨fun i => x.val (p.symm i),
    (Equiv.sum_comp p.symm (fun i => x.val i ^ k)).trans x.property.1,
    fun i => by simpa using x.property.2 (p.symm i)⟩
  left_inv x := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; funext i; simp

theorem local_power_ideal_class_card_of_unit (k : ℕ)
    (hk : 0<k) (hk0 : (k : R) ≠ 0) {s : ℕ} (x : Fin (s + 1) → R)
    (hx : ∃ i, IsUnit (x i)) (r : ℕ) :
    Nat.card (LocalPowerIdealClass k R ((powerDerivativeOrder R k + 1 + r) + powerDerivativeOrder R k)
      (powerDerivativeOrder R k + 1) (by omega) (s + 1) (∑ i, x i ^ k)
      (fun i => Ideal.Quotient.mk (maximalIdeal R ^ (powerDerivativeOrder R k + 1)) (x i))) =
        Nat.card (ResidueField R) ^ (s * (r + powerDerivativeOrder R k) + powerDerivativeOrder R k) := by
  classical
  obtain ⟨j, hj⟩ := hx
  let p := Equiv.swap (0 : Fin (s + 1)) j
  have hsum := Equiv.sum_comp p (fun i => x i ^ k)
  rw [Nat.card_congr (localPowerIdealClassPermute k _ _ _ _ _ p)]
  rw [← hsum]
  exact local_power_ideal_class_card_of_unit_first k hk hk0 (fun i => x (p i)) (by simpa [p] using hj) r

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.power_ideal_head_fiber_card

#print axioms WaringSiegel.WSL3.local_power_ideal_class_card_of_unit
