import WaringSiegel.WSL2MomentDifferencing
import WaringSiegel.WSL2MomentPowerFibers
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.Coset.Basic

/-!
# The actual finite-character average in the mixed sixth moment

Finite Pontryagin duality proves the exact average over all characters of a
finite residue group.  Cauchy is applied after this average, in each power-map
fiber.  There is no corresponding assertion about the original pointwise
square.  The final unit-power specialization keeps its exact algebraic kernel
cardinality, ready for separate local arithmetic estimates.
-/

noncomputable section
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL2

variable {A α : Type*} [AddCommGroup A] [Fintype A] [Fintype α]

def residueFiber (v : α → A) (b : A) : Finset α :=
  Finset.univ.filter (fun r => v r = b)

def residueFiberSum (v : α → A) (w : α → ℂ) (b : A) : ℂ :=
  ∑ r ∈ residueFiber v b, w r

def finiteCharacterSum (v : α → A) (w : α → ℂ) (ψ : AddChar A ℂ) : ℂ :=
  ∑ r, w r * ψ (v r)

theorem complex_ofReal_finite_average {β : Type*} [Fintype β] (f : β → ℝ) :
    ((𝔼 b, f b : ℝ) : ℂ) = 𝔼 b, (f b : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div,
    Complex.ofReal_sum, Complex.ofReal_natCast]

theorem finite_character_family_average_energy {H : Type*} [Fintype H]
    (v : α → A) (w : α → ℂ) (χ : H → AddChar A ℂ)
    (hχ : ∀ b, (𝔼 η, χ η b) = if b=0 then 1 else 0) :
    (𝔼 η, ‖finiteCharacterSum v w (χ η)‖^2) =
      ∑ p : α × α, if v p.1 = v p.2 then (w p.1 * conj (w p.2)).re else 0 := by
  have hcomplex : ((𝔼 η, ‖finiteCharacterSum v w (χ η)‖^2 : ℝ) : ℂ) =
      ∑ p : α × α, if v p.1 = v p.2 then w p.1 * conj (w p.2) else 0 := by
    rw [complex_ofReal_finite_average]
    simp only [finiteCharacterSum]
    simp only [finite_sum_norm_sq_pair_expansion, Finset.product_eq_sprod,
      Finset.univ_product_univ]
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    have hphase (η : H) :
        (w p.1 * χ η (v p.1)) * conj (w p.2 * χ η (v p.2)) =
          (w p.1 * conj (w p.2)) * χ η (v p.1 - v p.2) := by
      rw [map_mul, AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
      ring
    simp_rw [hphase]
    rw [← Finset.mul_expect, hχ]
    by_cases h : v p.1 = v p.2
    · simp [h]
    · simp [h, sub_eq_zero]
  have h := congrArg Complex.re hcomplex
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] using h

theorem finite_character_average_energy (v : α → A) (w : α → ℂ) :
    (𝔼 ψ : AddChar A ℂ, ‖finiteCharacterSum v w ψ‖^2) =
      ∑ p : α × α, if v p.1 = v p.2 then (w p.1 * conj (w p.2)).re else 0 :=
  finite_character_family_average_energy v w id (fun b => AddChar.expect_apply_eq_ite b)

theorem residue_fiber_sum_norm_sq (v : α → A) (w : α → ℂ) :
    (∑ b, ‖residueFiberSum v w b‖^2) =
      ∑ p : α × α, if v p.1 = v p.2 then (w p.1 * conj (w p.2)).re else 0 := by
  have hcomplex : ((∑ b, ‖residueFiberSum v w b‖^2 : ℝ) : ℂ) =
      ∑ p : α × α, if v p.1 = v p.2 then w p.1 * conj (w p.2) else 0 := by
    rw [Complex.ofReal_sum]
    simp only [residueFiberSum]
    simp only [finite_sum_norm_sq_pair_expansion, Finset.product_eq_sprod, Finset.sum_product]
    simp only [residueFiber, Finset.sum_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    simp [eq_comm]
  have h := congrArg Complex.re hcomplex
  simpa only [Complex.ofReal_re, Complex.re_sum, apply_ite, Complex.zero_re] using h

/-- The manuscript's exact finite kernel average, with a genuinely complete
character group and proved orthogonality. -/
theorem finite_character_average_fibers (v : α → A) (w : α → ℂ) :
    (𝔼 ψ : AddChar A ℂ, ‖finiteCharacterSum v w ψ‖^2) =
      ∑ b, ‖residueFiberSum v w b‖^2 := by
  rw [finite_character_average_energy, residue_fiber_sum_norm_sq]

theorem finite_character_family_average_fibers {H : Type*} [Fintype H]
    (v : α → A) (w : α → ℂ) (χ : H → AddChar A ℂ)
    (hχ : ∀ b, (𝔼 η, χ η b) = if b=0 then 1 else 0) :
    (𝔼 η, ‖finiteCharacterSum v w (χ η)‖^2) =
      ∑ b, ‖residueFiberSum v w b‖^2 := by
  rw [finite_character_family_average_energy v w χ hχ, residue_fiber_sum_norm_sq]

theorem residue_fiber_cauchy (v : α → A) (w : α → ℂ) (b : A) :
    ‖residueFiberSum v w b‖^2 ≤
      ((residueFiber v b).card : ℝ) * ∑ r ∈ residueFiber v b, ‖w r‖^2 := by
  have htri := norm_sum_le (residueFiber v b) w
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq (residueFiber v b)
    (fun _ => (1 : ℝ)) (fun r => ‖w r‖)
  exact hsq.trans (by simpa [residueFiberSum] using hcauchy)

theorem residue_fiber_sum_partition (v : α → A) (f : α → ℝ) :
    (∑ b, ∑ r ∈ residueFiber v b, f r) = ∑ r, f r := by
  simp only [residueFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Fiber multiplicity controls the averaged square.  No pointwise comparison
of the unaveraged sum is made. -/
theorem finite_character_average_le (v : α → A) (w : α → ℂ)
    (M : ℕ) (hM : ∀ b, (residueFiber v b).card ≤ M) :
    (𝔼 ψ : AddChar A ℂ, ‖finiteCharacterSum v w ψ‖^2) ≤
      (M : ℝ) * ∑ r, ‖w r‖^2 := by
  rw [finite_character_average_fibers]
  calc
    _ ≤ ∑ b, (M : ℝ) * ∑ r ∈ residueFiber v b, ‖w r‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact (residue_fiber_cauchy v w b).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hM b)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := by rw [← Finset.mul_sum, residue_fiber_sum_partition]

theorem finite_character_family_average_le {H : Type*} [Fintype H]
    (v : α → A) (w : α → ℂ) (χ : H → AddChar A ℂ)
    (hχ : ∀ b, (𝔼 η, χ η b) = if b=0 then 1 else 0)
    (M : ℕ) (hM : ∀ b, (residueFiber v b).card ≤ M) :
    (𝔼 η, ‖finiteCharacterSum v w (χ η)‖^2) ≤
      (M : ℝ) * ∑ r, ‖w r‖^2 := by
  rw [finite_character_family_average_fibers v w χ hχ,
    ← finite_character_average_fibers]
  exact finite_character_average_le v w M hM

/-- Unit-power residues satisfy the averaged Cauchy inequality with the exact
kernel size of the unit power map. -/
theorem finite_character_unit_power_average_le {Q : Type*} [CommRing Q] [Fintype Q]
    (k : ℕ) (w : Qˣ → ℂ) :
    (𝔼 ψ : AddChar Q ℂ,
      ‖finiteCharacterSum (fun r : Qˣ => (r : Q)^k) w ψ‖^2) ≤
      ((unitPowerKernel Q k).card : ℝ) * ∑ r : Qˣ, ‖w r‖^2 :=
  finite_character_average_le _ w _ (fun b => unit_power_fiber_card_le k b)

/-- The cubic specialization used to replace the cubic congruence by equality
of ordinary unit residues after finite-kernel averaging. -/
theorem finite_character_unit_cubic_average_le {Q : Type*} [CommRing Q] [Fintype Q]
    (w : Qˣ → ℂ) :
    (𝔼 ψ : AddChar Q ℂ,
      ‖finiteCharacterSum (fun r : Qˣ => (r : Q)^3) w ψ‖^2) ≤
      ((unitPowerKernel Q 3).card : ℝ) * ∑ r : Qˣ, ‖w r‖^2 :=
  finite_character_unit_power_average_le 3 w

end WaringSiegel.WSL2
