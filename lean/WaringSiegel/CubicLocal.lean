import WaringSiegel.CubicHensel
import WaringSiegel.CubicDyadicFinite

/-!
# Uniform local cubic representations

Every cubically eligible element of a Henselian local ring with finite residue
field is a sum of five cubes with a unit coordinate. If the residue field has
characteristic two, four cubes suffice. The characteristic-two proof combines
the Artin–Schreier finite-field theorem with actual simple-root Hensel lifting.
-/

noncomputable section

open scoped BigOperators NumberField
open IsLocalRing

namespace WaringSiegel

theorem three_isUnit_of_residue_char_two
    {R : Type*} [CommRing R] [IsLocalRing R] [CharP (ResidueField R) 2] :
    IsUnit (3 : R) := by
  apply (residue_ne_zero_iff_isUnit (3 : R)).mp
  rw [map_ofNat]
  have h3 : (3 : ResidueField R) = 1 := by
    calc
      (3 : ResidueField R) = 2 + 1 := by norm_num
      _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  rw [h3]
  exact one_ne_zero

theorem four_cubes_henselian_residue_char_two
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    [Finite (ResidueField R)] [CharP (ResidueField R) 2]
    {a : R} (ha : a ∈ cubeSpan R) :
    ∃ x : Fin 4 → R, (∑ i, x i ^ 3) = a ∧ ∃ i, IsUnit (x i) := by
  have hres := map_mem_cubeSpan (residue R) ha
  obtain ⟨x, hx, hu⟩ := four_cubes_finite_char_two_nonzero (ResidueField R) hres
  exact cube_tuple_lift_of_nonzero_residue three_isUnit_of_residue_char_two x hx hu

/-- Adding a zero coordinate preserves the cube sum and a unit coordinate. -/
theorem cube_tuple_with_unit_pad
    {R : Type*} [CommRing R] {s : ℕ} {a : R}
    (h : ∃ x : Fin s → R, (∑ i, x i ^ 3) = a ∧ ∃ i, IsUnit (x i)) :
    ∃ x : Fin (s + 1) → R, (∑ i, x i ^ 3) = a ∧ ∃ i, IsUnit (x i) := by
  obtain ⟨x, hx, i, hi⟩ := h
  refine ⟨Fin.cons 0 x, ?_, i.succ, ?_⟩
  · simpa [Fin.sum_univ_succ] using hx
  · simpa using hi

/-- A uniform five-cube local theorem, with no residue-characteristic split
remaining in the statement. -/
theorem five_cubes_henselian_finite_residue
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    [Finite (ResidueField R)] {a : R} (ha : a ∈ cubeSpan R) :
    ∃ x : Fin 5 → R, (∑ i, x i ^ 3) = a ∧ ∃ i, IsUnit (x i) := by
  by_cases h2 : IsUnit (2 : R)
  · exact five_cubes_tuple_with_unit h2 ha
  · have h20 : (2 : ResidueField R) = 0 := by
      have hn := (residue_ne_zero_iff_isUnit (2 : R)).not.mpr h2
      simpa only [map_ofNat, not_not] using hn
    letI : CharP (ResidueField R) 2 :=
      CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h20
    exact cube_tuple_with_unit_pad (four_cubes_henselian_residue_char_two ha)

/-- Padding is compatible with the actual completion-based local condition. -/
theorem LocalUnitSolvable.cubic_succ
    {K : Type*} [Field K] [NumberField K] {s : ℕ} {ν : 𝓞 K}
    (h : LocalUnitSolvable 3 s ν) : LocalUnitSolvable 3 (s + 1) ν := by
  intro v
  exact cube_tuple_with_unit_pad (h v)

end WaringSiegel

#print axioms WaringSiegel.four_cubes_henselian_residue_char_two
#print axioms WaringSiegel.five_cubes_henselian_finite_residue
