import WaringSiegel.WSL2MomentVinogradov
import Waring.External.GafniTao.WooleyTupleDisplacement

/-!
# Finite Fourier moments for arbitrary monomial nodes

The native integer argument averages over a finite residue grid.  This
module identifies that average with the literal Vinogradov count for any
finite family of residue-ring nodes.  No interval or ordering assumption is
used on the node set.
-/

noncomputable section
open Finset GafniTao
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {α : Type*} [Fintype α]

/-- The exact normalized finite Fourier moment, for any finite family of
monomial nodes in a nonzero residue ring. -/
theorem monomial_grid_mean_eq_count (q k s : ℕ) [NeZero q]
    (nodes : α → ZMod q) :
    ((q ^ k : ℕ) : ℝ)⁻¹ *
      ∑ a : Fin k → ZMod q,
        ‖∑ x : α, ZMod.stdAddChar
          (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) =
      (vinogradovCount k s nodes : ℝ) := by
  let value : α → Fin k → ZMod q := fun x j => nodes x ^ (j.val + 1)
  let disp := wooleyTupleDisplacement q k s value
  have hdisp (xy : (Fin s → α) × (Fin s → α)) :
      disp xy = 0 ↔ VinogradovEquations k s nodes xy.1 xy.2 := by
    simp only [disp, wooleyTupleDisplacement, value, funext_iff,
      Pi.zero_apply, sub_eq_zero, VinogradovEquations]
  have hphase (a : Fin k → ZMod q) (x : α) :
      ZMod.stdAddChar (∑ j : Fin k, a j * nodes x ^ (j.val + 1)) =
        wooleyPointCharacter q k value a x :=
    wooley_addChar_sum_eq_prod ZMod.stdAddChar _
  have hexpand (a : Fin k → ZMod q) :
      ((‖∑ x : α, ZMod.stdAddChar
          (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) : ℝ) : ℂ) =
        ∑ xy : (Fin s → α) × (Fin s → α),
          (1 : ℂ) * ∏ j, ZMod.stdAddChar (a j * disp xy j) := by
    simp_rw [hphase]
    rw [Complex.ofReal_pow, ← ford_pow_mul_conj_pow]
    have h := wooley_weighted_sum_abs_pow_expand s (fun _ : α => (1 : ℂ))
      (wooleyPointCharacter q k value a)
    simp only [one_mul, wooleyTupleCoefficient, Finset.prod_const_one,
      map_one, mul_one, wooley_tuple_pair_character] at h
    simpa only [one_mul, disp] using h
  have hcomplex :
      (((q ^ k : ℕ) : ℂ)⁻¹) *
        ∑ a : Fin k → ZMod q,
          ((‖∑ x : α, ZMod.stdAddChar
            (∑ j : Fin k, a j * nodes x ^ (j.val + 1))‖ ^ (2 * s) : ℝ) : ℂ) =
        (vinogradovCount k s nodes : ℂ) := by
    simp_rw [hexpand]
    rw [wooley_weighted_grid_average_eq_filter]
    simp_rw [hdisp]
    simp [vinogradovCount, Finset.sum_boole]
  apply Complex.ofReal_injective
  push_cast
  simpa only [Nat.cast_pow, Complex.ofReal_pow] using hcomplex

#print axioms monomial_grid_mean_eq_count

end WaringSiegel.WSL3
