import WaringSiegel.CubicLocalTargets

/-!
# Quantitative cubic lifting near a unit

The uniform neighborhood `x^3 + 9 m` consists of unit cubes whenever `x` is a
unit in a Henselian local ring with maximal ideal `m`. This includes residue
characteristic three; the proof transforms the equation into a monic cubic
with a simple residue root instead of assuming that 3 is a unit.
-/

noncomputable section

open Polynomial IsLocalRing
open scoped BigOperators

namespace WaringSiegel

/-- A target-independent neighborhood on which a unit cube can be adjusted. -/
def cubicStabilityIdeal (R : Type*) [CommRing R] [IsLocalRing R] : Ideal R :=
  Ideal.span ({9} : Set R) * maximalIdeal R

theorem cubic_correction_surjective
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    {x c : R} (hx : IsUnit x) (hc : c ∈ maximalIdeal R) :
    ∃ t : R, t ∈ maximalIdeal R ∧ 3 * t ^ 3 + 3 * x * t ^ 2 + x ^ 2 * t = c := by
  let f : R[X] := X ^ 3 -
    (C (x ^ 2) * X ^ 2 + C (3 * x * c) * X + C (3 * c ^ 2))
  have hf : f.Monic := by
    apply monic_X_pow_sub
    apply lt_of_le_of_lt (b := (2 : WithBot ℕ))
    · apply degree_add_le_of_degree_le
      · apply degree_add_le_of_degree_le
        · exact degree_C_mul_X_pow_le 2 _
        · exact (degree_C_mul_X_le _).trans (by decide)
      · exact degree_C_le.trans (by decide)
    · decide
  have hc0 : residue R c = 0 := (residue_eq_zero_iff c).mpr hc
  have hxn : residue R x ≠ 0 := (residue_ne_zero_iff_isUnit x).mpr hx
  have hroot : aeval (residue R x ^ 2) f = 0 := by
    simp [f, hc0]
    ring
  have hder : aeval (residue R x ^ 2) f.derivative ≠ 0 := by
    have he : aeval (residue R x ^ 2) f.derivative = residue R x ^ 4 := by
      simp [f, derivative_pow, hc0, map_ofNat]
      ring
    rw [he]
    exact pow_ne_zero _ hxn
  have hH := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨w, hw, hwr⟩ := hH f hf _ hroot hder
  have hwu : IsUnit w := (residue_ne_zero_iff_isUnit w).mp
    (hwr ▸ pow_ne_zero 2 hxn)
  have hw0 : w ^ 3 = x ^ 2 * w ^ 2 + 3 * x * c * w + 3 * c ^ 2 := by
    apply sub_eq_zero.mp
    simpa [f, Polynomial.IsRoot] using hw
  let t : R := c * ↑hwu.unit⁻¹
  have hwt : w * t = c := by
    have hinv : w * ↑hwu.unit⁻¹ = 1 := by
      simpa only [hwu.unit_spec] using Units.mul_inv hwu.unit
    calc
      w * t = c * (w * ↑hwu.unit⁻¹) := by dsimp [t]; ring
      _ = c := by rw [hinv, mul_one]
  have ht : 3 * t ^ 3 + 3 * x * t ^ 2 + x ^ 2 * t = c := by
    apply sub_eq_zero.mp
    apply (hwu.pow 3).mul_left_cancel
    rw [mul_zero]
    calc
      w ^ 3 * (3 * t ^ 3 + 3 * x * t ^ 2 + x ^ 2 * t - c) =
          3 * (w * t) ^ 3 + 3 * x * (w * t) ^ 2 * w +
            x ^ 2 * (w * t) * w ^ 2 - c * w ^ 3 := by ring
      _ = 0 := by rw [hwt, hw0]; ring
  have htr : residue R t = 0 := by simp [t, hc0]
  exact ⟨t, (residue_eq_zero_iff t).mp htr, ht⟩

theorem unit_cube_nine_maximalIdeal_perturbation
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    {x c : R} (hx : IsUnit x) (hc : c ∈ maximalIdeal R) :
    ∃ y : R, y ^ 3 = x ^ 3 + 9 * c ∧ residue R y = residue R x ∧ IsUnit y := by
  obtain ⟨t, htm, ht⟩ := cubic_correction_surjective hx hc
  have hxn : residue R x ≠ 0 := (residue_ne_zero_iff_isUnit x).mpr hx
  have htr : residue R t = 0 := (residue_eq_zero_iff t).mpr htm
  have hyr : residue R (x + 3 * t) = residue R x := by simp [htr]
  refine ⟨x + 3 * t, ?_, hyr, (residue_ne_zero_iff_isUnit _).mp (hyr ▸ hxn)⟩
  calc
    (x + 3 * t) ^ 3 = x ^ 3 + 9 * (3 * t ^ 3 + 3 * x * t ^ 2 + x ^ 2 * t) := by ring
    _ = x ^ 3 + 9 * c := by rw [ht]

/-- Perturbing every free coordinate in `9 m` leaves one unit coordinate
available to restore the exact cube sum. -/
theorem cube_sum_adjust_free_coordinates
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    {s : ℕ} (x : Fin (s + 1) → R) (hx : IsUnit (x 0))
    (y : Fin s → R)
    (hy : ∀ i, y i - x i.succ ∈ cubicStabilityIdeal R) :
    ∃ z : R, z ^ 3 + ∑ i, y i ^ 3 = ∑ i, x i ^ 3 ∧ IsUnit z := by
  let d : R := ∑ i, (x i.succ ^ 3 - y i ^ 3)
  have hd : d ∈ cubicStabilityIdeal R := by
    apply Ideal.sum_mem
    intro i _
    have hi := (cubicStabilityIdeal R).neg_mem (hy i)
    have hm := (cubicStabilityIdeal R).mul_mem_left
      (x i.succ ^ 2 + x i.succ * y i + y i ^ 2) hi
    convert hm using 1; ring
  obtain ⟨c, hc, hcd⟩ := Ideal.mem_span_singleton_mul.mp hd
  obtain ⟨z, hz, -, hzu⟩ := unit_cube_nine_maximalIdeal_perturbation hx hc
  refine ⟨z, ?_, hzu⟩
  rw [hz, hcd, Fin.sum_univ_succ]
  simp only [d, Finset.sum_sub_distrib]
  abel

theorem cube_tuple_unit_first
    {R : Type*} [CommRing R] {s : ℕ} {a : R}
    (h : ∃ x : Fin (s + 1) → R, (∑ i, x i ^ 3) = a ∧ ∃ i, IsUnit (x i)) :
    ∃ x : Fin (s + 1) → R, (∑ i, x i ^ 3) = a ∧ IsUnit (x 0) := by
  classical
  obtain ⟨x, hx, j, hj⟩ := h
  let e : Fin (s + 1) ≃ Fin (s + 1) := Equiv.swap 0 j
  refine ⟨fun i => x (e i), ?_, ?_⟩
  · exact (Equiv.sum_comp e (fun i => x i ^ 3)).trans hx
  · simpa [e] using hj

end WaringSiegel

#print axioms WaringSiegel.unit_cube_nine_maximalIdeal_perturbation
#print axioms WaringSiegel.cube_sum_adjust_free_coordinates
