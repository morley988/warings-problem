import WaringSiegel.WSL3MomentLocalPowerStability
import WaringSiegel.WSL3MomentLocalPowerCount

/-!
# Actual all-degree local counts, including every ramified prime

The free-coordinate injection is adapted from the checked cubic count.
The general k-squared perturbation theorem supplies its exact local input.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

theorem local_power_count_lower_of_unit_tuple_ramified
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k : ℕ) (hk : 0<k)
    {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0))
    (E : ℕ) (hE : maximalIdeal R ^ E ≤ powerStabilityIdeal R k) (n : ℕ) :
    Nat.card (ResidueField R) ^ (s * n) ≤
      localPowerSolutionCount R (maximalIdeal R ^ (n + E)) k (s + 1) (∑ i, x i ^ k) := by
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
      y b i - x i.succ ∈ powerStabilityIdeal R k := by
    apply hE
    simp only [y, add_sub_cancel_left]
    exact (maximalIdeal R ^ E).mul_mem_right _ (Ideal.pow_mem_pow hπm E)
  have hzexists (b : Fin s → R ⧸ maximalIdeal R ^ n) :
      ∃ z : R, z ^ k + ∑ i, y b i ^ k = ∑ i, x i ^ k ∧ IsUnit z :=
    power_sum_adjust_free_coordinates_ramified k hk x hx (y b) (hy b)
  choose z hz hzu using hzexists
  let out (b : Fin s → R ⧸ maximalIdeal R ^ n) :
      LocalPowerSolutions R (maximalIdeal R ^ (n + E)) k (s + 1) (∑ i, x i ^ k) :=
    ⟨fun i => Ideal.Quotient.mk (maximalIdeal R ^ (n + E))
      ((Fin.cons (z b) (y b) : Fin (s + 1) → R) i), by
      have hs : (∑ i, (Fin.cons (z b) (y b) i) ^ k) = ∑ i, x i ^ k := by
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
    _ ≤ localPowerSolutionCount R (maximalIdeal R ^ (n + E)) k (s + 1) (∑ i, x i ^ k) :=
      Nat.card_le_card_of_injective out hout


#print axioms local_power_count_lower_of_unit_tuple_ramified
end WaringSiegel.WSL3
