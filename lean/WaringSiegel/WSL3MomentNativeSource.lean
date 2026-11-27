import WaringSiegel.WSL3MomentFiniteMean
import WaringSiegel.WSL2MomentIntegerSource
import Waring.External.GafniTao.WooleySourceCriticalBase
import Waring.External.GafniTao.WooleySourceToPadic

/-!
# The native critical congruence bound on arbitrary finite integer sources

The coefficient source is the actual finitely supported sequence from WSL2.
Its global and conditioned means are identified with the exact native
definitions before applying the replayed Corollary 3.2.
-/

noncomputable section
open Finset GafniTao
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {α : Type*} [Fintype α]

theorem integerSource_monomial_mean (q k s : ℕ) [NeZero q] [Nonempty α]
    (labels : α → ℤ) (hinj : Function.Injective labels) :
    wooleySourcePolynomialMean s q (wooleyMonomialPolynomialSystem k)
      (integerNodeSource labels) =
      (vinogradovCount k s (fun x => (labels x : ZMod q)) : ℝ) /
        (Fintype.card α : ℝ) ^ s := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hmass : wooleySourceMassSq (integerNodeSource labels) =
      (Fintype.card α : ℝ) := integerNodeSource_mass labels hinj
  have hnorm (a : Fin k → ZMod q) :
      ‖wooleySourceNormalizedPolynomialSum (wooleyMonomialPolynomialSystem k)
        (integerNodeSource labels) a‖ ^ (2 * s) =
      ((Fintype.card α : ℝ) ^ s)⁻¹ *
        ‖∑ x : α, ZMod.stdAddChar
          (∑ j : Fin k, a j * (labels x : ZMod q) ^ (j.val + 1))‖ ^ (2 * s) := by
    rw [wooleySourceNormalizedPolynomialSum, hmass, if_neg (ne_of_gt hN),
      wooleySourcePolynomialSum, integerNodeSource_sum labels hinj]
    simp only [wooleySourcePolynomialPhase, wooleyMonomialPolynomialSystem,
      Polynomial.eval_pow, Polynomial.eval_X, Int.cast_pow]
    rw [norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
      pow_mul, Real.sq_sqrt hN.le]
  unfold wooleySourcePolynomialMean
  simp_rw [hnorm]
  rw [← Finset.mul_sum]
  calc
    _ = ((Fintype.card α : ℝ) ^ s)⁻¹ *
        (((q ^ k : ℕ) : ℝ)⁻¹ * ∑ a : Fin k → ZMod q,
          ‖∑ x : α, ZMod.stdAddChar
            (∑ j : Fin k, a j * (labels x : ZMod q) ^ (j.val + 1))‖ ^ (2 * s)) := by ring
    _ = _ := by rw [monomial_grid_mean_eq_count]; ring

theorem integerSource_conditioned_mean (q qH k s : ℕ)
    [NeZero q] [NeZero qH] [Nonempty α]
    (labels : α → ℤ)
    (hinj : Function.Injective (fun x => (labels x : ZMod qH)))
    (φ : WooleyPolynomialSystem k) :
    wooleySourcePolynomialConditionedMean s q qH φ (integerNodeSource labels) = 1 := by
  have hlabels : Function.Injective labels := fun x y h => hinj (congrArg (fun z : ℤ => (z : ZMod qH)) h)
  have hmass : (∑ n ∈ (integerNodeSource labels).support, ‖integerNodeSource labels n‖ ^ 2) ≠ 0 := by
    rw [integerNodeSource_mass labels hlabels]
    exact_mod_cast Fintype.card_ne_zero
  have h := integerNodeSource_conditioned_mean (β := Fin k → ZMod q) labels hinj
    (wooleySourcePolynomialPhase φ) (wooleySourcePolynomialPhase_norm φ) s
  simpa only [wooleySourcePolynomialConditionedMean, wooleySourceMassSq,
    wooleySourceResidueMassSq, wooleySourceNormalizedPolynomialResidueSum,
    wooleySourcePolynomialResidueSum, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, if_neg hmass] using h

/-- Native critical congruence VMVT for any finite integer family that is
injective modulo the lower prime power.  The constants are independent of
the family, its size, and its integer representatives. -/
theorem native_monomial_modular_count_bound (k p : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (H : ℕ) {α : Type*} [Fintype α] (labels : α → ℤ), B0 ≤ k * H →
        Function.Injective (fun x => (labels x : ZMod (p ^ H))) →
        (vinogradovCount k (wooleyTriangular k)
          (fun x => (labels x : ZMod (p ^ (k * H)))) : ℝ) ≤
          C * (p ^ (k * H) : ℝ) ^ δ * (Fintype.card α : ℝ) ^ (wooleyTriangular k) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨C, hC, B0, hmain⟩ := wooleyPolynomialCorollary32_native
    k p hp hk hkp 1 δ (by norm_num) hδ
  refine ⟨C, hC, B0, ?_⟩
  intro H α inst labels hB hinj
  have hs : 1 ≤ wooleyTriangular k := by
    simp only [wooleyTriangular]
    have : 2 ≤ k * (k + 1) := by nlinarith
    omega
  cases isEmpty_or_nonempty α with
  | inl hempty =>
    letI : IsEmpty α := hempty
    haveI : IsEmpty (Fin (wooleyTriangular k) → α) :=
      ⟨fun f => isEmptyElim (f ⟨0, hs⟩)⟩
    simp [vinogradovCount, Fintype.card_eq_zero, Nat.ne_of_gt hs]
  | inr hnonempty =>
    letI : Nonempty α := hnonempty
    have hlabels : Function.Injective labels := fun x y h =>
      hinj (congrArg (fun z : ℤ => (z : ZMod (p ^ H))) h)
    have hPhi : (wooleyMonomialPolynomialSystem k).InPhiTau p (k * H) 1 := by
      refine ⟨k * H, wooleyMonomialPolynomialSystem_spaced k p (k * H), ?_⟩
      norm_num
    have hbound := hmain (k * H) (wooleyMonomialPolynomialSystem k)
      (integerNodeSource labels) hB hPhi (integerNodeSource_admissible labels)
    simp only [wooley_mul_ceilDiv_self hk] at hbound
    rw [integerSource_conditioned_mean _ _ _ _ labels hinj,
      integerSource_monomial_mean _ _ _ labels hlabels, mul_one] at hbound
    have hN : (0 : ℝ) < (Fintype.card α : ℝ) ^ (wooleyTriangular k) := by
      have : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
      positivity
    exact (div_le_iff₀ hN).mp hbound

#print axioms native_monomial_modular_count_bound

end WaringSiegel.WSL3
