import WaringSiegel.WSL2LocalLift
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Actual counts of cubic solutions modulo ideal powers

The types and counts below are literal tuples over the indicated quotient
ring. The quantitative lower bounds will be obtained by an injection of free
coordinates, using the uniform unit-cube neighborhood from `WSL2LocalLift`.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators

namespace WaringSiegel

def LocalCubicSolutions (R : Type*) [CommRing R] (I : Ideal R) (s : ℕ) (a : R) :=
  {x : Fin s → R ⧸ I // (∑ i, x i ^ 3) = Ideal.Quotient.mk I a}

def localCubicSolutionCount (R : Type*) [CommRing R] (I : Ideal R) (s : ℕ) (a : R) : ℕ :=
  Nat.card (LocalCubicSolutions R I s a)

instance localCubicSolutions_finite
    {R : Type*} [CommRing R] (I : Ideal R) (s : ℕ) (a : R) [Finite (R ⧸ I)] :
    Finite (LocalCubicSolutions R I s a) := by
  unfold LocalCubicSolutions
  infer_instance

theorem dvr_power_quotient_card
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ maximalIdeal R ^ n) = Nat.card (ResidueField R) ^ n := by
  simpa only [Submodule.cardQuot_apply] using
    (cardQuot_pow_of_prime (P := maximalIdeal R) (i := n)
      (IsDiscreteValuationRing.not_a_field R))

theorem dvr_power_quotient_finite
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (ResidueField R)] (n : ℕ) : Finite (R ⧸ maximalIdeal R ^ n) := by
  apply Nat.finite_of_card_ne_zero
  rw [dvr_power_quotient_card]
  exact pow_ne_zero _ Nat.card_pos.ne'

/-- Multiplication by a uniformizer power injects the corresponding quotient
into the higher-precision quotient. -/
theorem uniformizer_power_cancel_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {π d : R} (hπ : Irreducible π) (E n : ℕ) :
    π ^ E * d ∈ maximalIdeal R ^ (n + E) ↔ d ∈ maximalIdeal R ^ n := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_add,
    mul_comm (π ^ n), mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)]

/-- The stability exponent depends only on the local ring, not on the target
or a chosen solution. It is the exponent of the ideal `9 m`. -/
theorem exists_cubic_stability_exponent
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h9 : (9 : R) ≠ 0) :
    ∃ E : ℕ, 0 < E ∧ maximalIdeal R ^ E = cubicStabilityIdeal R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hspan : Ideal.span ({9} : Set R) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using h9
  have hJ : cubicStabilityIdeal R ≠ ⊥ :=
    mul_ne_zero hspan (IsDiscreteValuationRing.not_a_field R)
  obtain ⟨E, hE⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hπ
  have hmE : maximalIdeal R ^ E = cubicStabilityIdeal R := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact hE.symm
  refine ⟨E, ?_, hmE⟩
  by_contra he
  have he0 : E = 0 := Nat.eq_zero_of_not_pos he
  have hsub : cubicStabilityIdeal R ≤ maximalIdeal R := Ideal.mul_le_left
  rw [← hmE, he0, pow_zero, Ideal.one_eq_top] at hsub
  exact (inferInstance : (maximalIdeal R).IsMaximal).ne_top (top_le_iff.mp hsub)

/-- The precision in the manuscript: `2 v(3) + 1`, with the normalized DVR
additive valuation. The nonzero condition on 3 is required only by theorems. -/
def cubicLocalPrecision (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : ℕ :=
  2 * (IsDiscreteValuationRing.addVal R (3 : R)).toNat + 1

theorem cubicLocalPrecision_pos
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    0 < cubicLocalPrecision R := Nat.zero_lt_succ _

theorem cubic_stability_ideal_eq_power
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h3 : (3 : R) ≠ 0) :
    maximalIdeal R ^ cubicLocalPrecision R = cubicStabilityIdeal R := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨τ, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h3 hπ
  have hv : IsDiscreteValuationRing.addVal R (3 : R) = τ :=
    IsDiscreteValuationRing.addVal_def _ u hπ τ hu
  have h9 : (9 : R) = (↑(u ^ 2) : R) * π ^ (2 * τ) := by
    calc
      (9 : R) = (3 : R) ^ 2 := by ring
      _ = (↑u * π ^ τ) ^ 2 := by rw [hu]
      _ = (↑(u ^ 2) : R) * π ^ (2 * τ) := by
        simp only [Units.val_pow_eq_pow_val, mul_pow, Nat.mul_comm 2 τ, pow_mul]
  have hspan : Ideal.span ({9} : Set R) = maximalIdeal R ^ (2 * τ) := by
    rw [h9, Ideal.span_singleton_mul_left_unit (u ^ 2).isUnit,
      hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  simp only [cubicLocalPrecision, hv, ENat.toNat_coe, cubicStabilityIdeal, hspan, pow_succ]

/-- Each of the `s` free coordinates contributes `q^n` distinct choices modulo
`m^(n+E)`. The remaining unit coordinate restores the exact equation. -/
theorem local_cubic_count_lower_of_unit_tuple
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0))
    (E : ℕ) (hE : maximalIdeal R ^ E ≤ cubicStabilityIdeal R) (n : ℕ) :
    Nat.card (ResidueField R) ^ (s * n) ≤
      localCubicSolutionCount R (maximalIdeal R ^ (n + E)) (s + 1) (∑ i, x i ^ 3) := by
  classical
  letI := dvr_power_quotient_finite (R := R) (n + E)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπm : π ∈ maximalIdeal R := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hreps : ∀ b : R ⧸ maximalIdeal R ^ n,
      ∃ r : R, Ideal.Quotient.mk (maximalIdeal R ^ n) r = b :=
    Ideal.Quotient.mk_surjective
  choose rep hrep using hreps
  let y (b : Fin s → R ⧸ maximalIdeal R ^ n) (i : Fin s) : R :=
    x i.succ + π ^ E * rep (b i)
  have hy (b : Fin s → R ⧸ maximalIdeal R ^ n) (i : Fin s) :
      y b i - x i.succ ∈ cubicStabilityIdeal R := by
    apply hE
    simp only [y, add_sub_cancel_left]
    exact (maximalIdeal R ^ E).mul_mem_right _ (Ideal.pow_mem_pow hπm E)
  have hzexists (b : Fin s → R ⧸ maximalIdeal R ^ n) :
      ∃ z : R, z ^ 3 + ∑ i, y b i ^ 3 = ∑ i, x i ^ 3 ∧ IsUnit z :=
    cube_sum_adjust_free_coordinates x hx (y b) (hy b)
  choose z hz hzu using hzexists
  let out (b : Fin s → R ⧸ maximalIdeal R ^ n) :
      LocalCubicSolutions R (maximalIdeal R ^ (n + E)) (s + 1) (∑ i, x i ^ 3) :=
    ⟨fun i => Ideal.Quotient.mk (maximalIdeal R ^ (n + E))
      ((Fin.cons (z b) (y b) : Fin (s + 1) → R) i), by
      have hs : (∑ i, (Fin.cons (z b) (y b) i) ^ 3) = ∑ i, x i ^ 3 := by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] using hz b
      simpa only [map_sum, map_pow] using
        congrArg (Ideal.Quotient.mk (maximalIdeal R ^ (n + E))) hs⟩
  have hout : Function.Injective out := by
    intro b d hbd
    funext i
    have hi := congrArg (fun t => t.val i.succ) hbd
    change Ideal.Quotient.mk (maximalIdeal R ^ (n + E)) (y b i) =
      Ideal.Quotient.mk (maximalIdeal R ^ (n + E)) (y d i) at hi
    have hdiff : π ^ E * (rep (b i) - rep (d i)) ∈ maximalIdeal R ^ (n + E) := by
      convert Ideal.Quotient.eq.mp hi using 1 <;> dsimp [y] <;> ring
    have hsmall := (uniformizer_power_cancel_mem hπ E n).mp hdiff
    have hquot := Ideal.Quotient.eq.mpr hsmall
    simpa only [hrep] using hquot
  calc
    Nat.card (ResidueField R) ^ (s * n) =
        Nat.card (Fin s → R ⧸ maximalIdeal R ^ n) := by
      rw [Nat.card_fun, Nat.card_fin, dvr_power_quotient_card, ← pow_mul, Nat.mul_comm]
    _ ≤ localCubicSolutionCount R (maximalIdeal R ^ (n + E)) (s + 1) (∑ i, x i ^ 3) :=
      Nat.card_le_card_of_injective out hout

end WaringSiegel

#print axioms WaringSiegel.exists_cubic_stability_exponent
#print axioms WaringSiegel.cubic_stability_ideal_eq_power
#print axioms WaringSiegel.local_cubic_count_lower_of_unit_tuple
