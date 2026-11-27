import WaringSiegel.WSL2LocalChart
import WaringSiegel.WSL2LocalScaling

/-!
# Cubic precision charts at primes over 3

On the neighborhood `x + 3m` of a unit, cubing loses exactly the valuation of
3 in precision. No invertibility assumption on 3 is used.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

def cubicBranchIdeal (R : Type*) [CommRing R] [IsLocalRing R] : Ideal R :=
  Ideal.span ({3} : Set R) * maximalIdeal R

theorem cube_sub_mem_stability_of_branch
    {R : Type*} [CommRing R] [IsLocalRing R] {x y : R}
    (hy : y - x ∈ cubicBranchIdeal R) : y ^ 3 - x ^ 3 ∈ cubicStabilityIdeal R := by
  obtain ⟨t, ht, he⟩ := Ideal.mem_span_singleton_mul.mp hy
  have hy' : y = x + 3 * t := by rw [he]; ring
  rw [hy']
  apply Ideal.mem_span_singleton_mul.mpr
  refine ⟨cubicCorrection x t, cubicCorrection_mem_maximalIdeal x ht, ?_⟩
  dsimp [cubicCorrection]
  ring

theorem unit_cube_stability_branch
    {R : Type*} [CommRing R] [HenselianLocalRing R] {x a : R}
    (hx : IsUnit x) (ha : a - x ^ 3 ∈ cubicStabilityIdeal R) :
    ∃ y : R, y ^ 3 = a ∧ y - x ∈ cubicBranchIdeal R := by
  obtain ⟨c, hc, he⟩ := Ideal.mem_span_singleton_mul.mp ha
  obtain ⟨t, ht, hg⟩ := cubic_correction_surjective hx hc
  refine ⟨x + 3 * t, ?_, ?_⟩
  · have hdiff : (x + 3 * t) ^ 3 - x ^ 3 = 9 * c := by
      rw [← hg]
      ring
    rw [he] at hdiff
    exact sub_left_inj.mp hdiff
  · apply Ideal.mem_span_singleton_mul.mpr
    exact ⟨t, ht, by ring⟩

/-- Exact first-derivative precision on the cubic branch. -/
theorem cube_sub_mem_three_mul_iff_of_branch
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h3 : (3 : R) ≠ 0) {x y : R} (hx : IsUnit x)
    (hy : y - x ∈ cubicBranchIdeal R) (I : Ideal R) :
    y ^ 3 - x ^ 3 ∈ Ideal.span ({3} : Set R) * I ↔ y - x ∈ I := by
  obtain ⟨t, ht, he⟩ := Ideal.mem_span_singleton_mul.mp hy
  have hy' : y = x + 3 * t := by rw [he]; ring
  let B : R := x ^ 2 + 3 * x * t + 3 * t ^ 2
  have hB : IsUnit B := by
    apply (residue_ne_zero_iff_isUnit B).mp
    have ht0 := (residue_eq_zero_iff t).mpr ht
    simpa [B, ht0] using pow_ne_zero 2 ((residue_ne_zero_iff_isUnit x).mpr hx)
  have hfactor : y ^ 3 - x ^ 3 = 3 * (B * (y - x)) := by
    rw [hy']
    dsimp [B]
    ring
  rw [hfactor, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨c, hc, he⟩
    have he' : c = B * (y - x) := mul_left_cancel₀ h3 he
    rw [he'] at hc
    exact (I.unit_mul_mem_iff_mem hB).mp hc
  · intro h
    exact ⟨B * (y - x), (I.unit_mul_mem_iff_mem hB).mpr h, rfl⟩

def cubicDerivativeOrder (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : ℕ :=
  (IsDiscreteValuationRing.addVal R (3 : R)).toNat

theorem span_three_eq_maximalIdeal_pow
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h3 : (3 : R) ≠ 0) :
    Ideal.span ({3} : Set R) = maximalIdeal R ^ cubicDerivativeOrder R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨τ, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h3 hπ
  have hv : IsDiscreteValuationRing.addVal R (3 : R) = τ :=
    IsDiscreteValuationRing.addVal_def _ u hπ τ hu
  simp only [cubicDerivativeOrder, hv, ENat.toNat_coe]
  rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit, hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow]

theorem cubicBranchIdeal_eq_power
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h3 : (3 : R) ≠ 0) :
    cubicBranchIdeal R = maximalIdeal R ^ (cubicDerivativeOrder R + 1) := by
  rw [cubicBranchIdeal, span_three_eq_maximalIdeal_pow R h3, pow_succ]

theorem unit_cube_congruence_precision
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h3 : (3 : R) ≠ 0) {x y : R} (hx : IsUnit x)
    (hy : y - x ∈ maximalIdeal R ^ (cubicDerivativeOrder R + 1)) (n : ℕ) :
    y ^ 3 - x ^ 3 ∈ maximalIdeal R ^ (n + cubicDerivativeOrder R) ↔
      y - x ∈ maximalIdeal R ^ n := by
  have h := cube_sub_mem_three_mul_iff_of_branch h3 hx
    ((cubicBranchIdeal_eq_power R h3).symm ▸ hy) (maximalIdeal R ^ n)
  rwa [span_three_eq_maximalIdeal_pow R h3, ← pow_add, Nat.add_comm] at h

def CubicRootBranch
    (R : Type*) [CommRing R] [IsLocalRing R] (e L : ℕ) (hLe : L ≤ e) (a x : R) :=
  {z : R ⧸ maximalIdeal R ^ e // z ^ 3 = Ideal.Quotient.mk _ a ∧
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) z =
      Ideal.Quotient.mk (maximalIdeal R ^ L) x}

/-- A unit-root branch has exactly `q^v(3)` roots at every adequate precision. -/
theorem cubic_root_branch_card_of_root
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (ResidueField R)] (h3 : (3 : R) ≠ 0) {x : R} (hx : IsUnit x)
    (n : ℕ) (hn : cubicDerivativeOrder R + 1 ≤ n) :
    Nat.card (CubicRootBranch R (n + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) (x ^ 3) x) =
        Nat.card (ResidueField R) ^ cubicDerivativeOrder R := by
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_add_right n (cubicDerivativeOrder R)))
  have he (z : R ⧸ maximalIdeal R ^ (n + cubicDerivativeOrder R)) :
      (z ^ 3 = Ideal.Quotient.mk _ (x ^ 3) ∧
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega :
          cubicDerivativeOrder R + 1 ≤ n + cubicDerivativeOrder R)) z =
            Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) x) ↔
      f z = Ideal.Quotient.mk (maximalIdeal R ^ n) x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [f, Ideal.Quotient.factor_mk, ← map_pow, Ideal.Quotient.eq]
    constructor
    · rintro ⟨hc, hb⟩
      exact (unit_cube_congruence_precision h3 hx hb n).mp hc
    · intro hc
      have hb : y - x ∈ maximalIdeal R ^ (cubicDerivativeOrder R + 1) :=
        Ideal.pow_le_pow_right hn hc
      exact ⟨(unit_cube_congruence_precision h3 hx hb n).mpr hc, hb⟩
  unfold CubicRootBranch
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact dvr_reduction_fiber_card n (cubicDerivativeOrder R) _

/-- The same exact root count applies to every target in the guaranteed cubic
neighborhood, without assuming it is already presented as a cube. -/
theorem cubic_root_branch_card
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (h3 : (3 : R) ≠ 0) {x a : R} (hx : IsUnit x)
    (ha : a - x ^ 3 ∈ cubicStabilityIdeal R)
    (n : ℕ) (hn : cubicDerivativeOrder R + 1 ≤ n) :
    Nat.card (CubicRootBranch R (n + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) a x) =
        Nat.card (ResidueField R) ^ cubicDerivativeOrder R := by
  obtain ⟨y, hy, hyx⟩ := unit_cube_stability_branch hx ha
  have hyx' : y - x ∈ maximalIdeal R ^ (cubicDerivativeOrder R + 1) :=
    (cubicBranchIdeal_eq_power R h3) ▸ hyx
  have hr : residue R y = residue R x := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.pow_le_self (Nat.succ_ne_zero _) hyx'
  have hyu : IsUnit y := (residue_ne_zero_iff_isUnit y).mp
    (hr ▸ (residue_ne_zero_iff_isUnit x).mpr hx)
  have hq : Ideal.Quotient.mk (maximalIdeal R ^ (cubicDerivativeOrder R + 1)) y =
      Ideal.Quotient.mk _ x := Ideal.Quotient.eq.mpr hyx'
  have he : CubicRootBranch R (n + cubicDerivativeOrder R)
      (cubicDerivativeOrder R + 1) (by omega) a x =
      CubicRootBranch R (n + cubicDerivativeOrder R)
        (cubicDerivativeOrder R + 1) (by omega) (y ^ 3) y := by
    unfold CubicRootBranch
    rw [hy, hq]
  rw [he]
  exact cubic_root_branch_card_of_root h3 hyu n hn

end WaringSiegel

#print axioms WaringSiegel.unit_cube_congruence_precision

#print axioms WaringSiegel.cubic_root_branch_card
