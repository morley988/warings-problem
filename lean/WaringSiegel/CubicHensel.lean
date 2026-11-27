import WaringSiegel.CompletionHensel
import WaringSiegel.CompletionCubes
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Lifting nonsingular residue cube tuples

For a finite tuple whose sum of cubes has the desired residue, a nonzero
residue coordinate and the unit condition on 3 allow Hensel lifting in that
one coordinate. The other coordinates are arbitrary lifts of their residues.
-/

noncomputable section

open scoped NumberField BigOperators
open Polynomial IsLocalRing

namespace WaringSiegel

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

theorem cube_lift_of_nonzero_residue
    (h3 : IsUnit (3 : R)) {a : R} {x : ResidueField R}
    (hx : x ^ 3 = residue R a) (hx0 : x ≠ 0) :
    ∃ y : R, y ^ 3 = a ∧ residue R y = x ∧ IsUnit y := by
  let f : R[X] := X ^ 3 - C a
  have hf : f.Monic := monic_X_pow_sub_C a (by decide)
  have hroot : aeval x f = 0 := by
    simp [f, hx]
  have h3r : (3 : ResidueField R) ≠ 0 := by
    simpa only [map_ofNat] using (h3.map (residue R)).ne_zero
  have hder : aeval x f.derivative ≠ 0 := by
    have he : aeval x f.derivative = 3 * x ^ 2 := by
      simp [f, derivative_pow, map_ofNat]
    rw [he]
    exact mul_ne_zero h3r (pow_ne_zero 2 hx0)
  have hH := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨y, hy, hyr⟩ := hH f hf x hroot hder
  refine ⟨y, ?_, hyr, (residue_ne_zero_iff_isUnit y).mp (hyr ▸ hx0)⟩
  exact sub_eq_zero.mp (by simpa [f, Polynomial.IsRoot] using hy)

theorem cube_tuple_lift_of_nonzero_residue
    (h3 : IsUnit (3 : R)) {s : ℕ} {a : R}
    (x : Fin s → ResidueField R)
    (hsum : (∑ i, x i ^ 3) = residue R a)
    (hunit : ∃ i, x i ≠ 0) :
    ∃ y : Fin s → R, (∑ i, y i ^ 3) = a ∧ ∃ i, IsUnit (y i) := by
  classical
  choose y hy using (fun i => residue_surjective (x i))
  obtain ⟨j, hj⟩ := hunit
  let b : R := a - ∑ i ∈ Finset.univ.erase j, y i ^ 3
  have hb : x j ^ 3 = residue R b := by
    simp only [b, map_sub, map_sum, map_pow, hy]
    rw [← hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    abel
  obtain ⟨z, hz, -, hzu⟩ := cube_lift_of_nonzero_residue h3 hb hj
  refine ⟨Function.update y j z, ?_, j, ?_⟩
  · have hpow : (fun i => (Function.update y j z i) ^ 3) =
        Function.update (fun i => y i ^ 3) j (z ^ 3) := by
      ext i
      by_cases h : i = j <;> simp only [Function.update_apply, h, if_true, if_false]
    rw [hpow, Finset.sum_update_of_mem (Finset.mem_univ j), hz]
    simp only [b, Finset.sdiff_singleton_eq_erase]
    abel
  · simpa using hzu

variable {K : Type*} [Field K] [NumberField K]

/-- Literal Hensel lifting in the completed integer ring of a number field.
The Henselian instance is supplied by the proved completion theorem. -/
theorem cube_tuple_lift_in_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h3 : IsUnit (3 : v.adicCompletionIntegers K))
    {s : ℕ} {a : v.adicCompletionIntegers K}
    (x : Fin s → ResidueField (v.adicCompletionIntegers K))
    (hsum : (∑ i, x i ^ 3) = residue (v.adicCompletionIntegers K) a)
    (hunit : ∃ i, x i ≠ 0) :
    ∃ y : Fin s → v.adicCompletionIntegers K,
      (∑ i, y i ^ 3) = a ∧ ∃ i, IsUnit (y i) := by
  letI := completionIntegers_henselianLocalRing v
  exact cube_tuple_lift_of_nonzero_residue h3 x hsum hunit

end WaringSiegel

#print axioms WaringSiegel.cube_tuple_lift_in_completion
