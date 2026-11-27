/-
The disjoint-ball proof below adapts Mathlib's
`Besicovitch.card_le_of_separated` (Sébastien Gouëzel, 2021),
released under Apache 2.0, to arbitrary separation and radius.
-/
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# WSL2: quantitative packing in a finite-dimensional normed space

These are actual cardinality bounds proved by disjoint Haar-measure balls.
They will be applied to the rescaled mixed embedding of a fractional ideal.
-/

noncomputable section
open Metric Set Module MeasureTheory
open scoped ENNReal Topology

namespace WaringSiegel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open scoped Function in
theorem packing_mass_bound (s : Finset E) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) * (δ / 2) ^ finrank ℝ E ≤ (R + δ / 2) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hhalf : 0 < δ / 2 := half_pos hδ
  have houter : 0 < R + δ / 2 := by linarith
  let A := ⋃ c ∈ s, ball (c : E) (δ / 2)
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have h := hsep c hc d hd hcd
    linarith
  have hsub : A ⊆ ball (0 : E) (R + δ / 2) := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith [hs c hc]
  have hmass :
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal ((R + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1) =
          μ A := by
        rw [show A = ⋃ c ∈ s, ball (c : E) (δ / 2) from rfl,
          measure_biUnion_finset hdisj fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hhalf]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (R + δ / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((R + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ houter]
  have hcancel : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + δ / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_right (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hmass
  have hreal := ENNReal.toReal_le_of_le_ofReal
    (pow_nonneg houter.le (finrank ℝ E)) hcancel
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hhalf.le _)] using hreal

theorem packing_card_bound (s : Finset E) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (1 + 2 * R / δ) ^ finrank ℝ E := by
  have h := packing_mass_bound s R δ hR hδ hs hsep
  have hdiv := (le_div_iff₀ (pow_pos (half_pos hδ) (finrank ℝ E))).mpr h
  rw [← div_pow] at hdiv
  have heq : (R + δ / 2) / (δ / 2) = 1 + 2 * R / δ := by
    field_simp
    <;> ring
  simpa only [heq] using hdiv

theorem packing_unit_ball_bound (s : Finset E) (δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (3 : ℝ) ^ finrank ℝ E *
      (1 + 1 / δ ^ finrank ℝ E) := by
  have h := packing_card_bound s 1 δ zero_le_one hδ hs hsep
  simp only [mul_one] at h
  have hp : 0 < δ ^ finrank ℝ E := pow_pos hδ _
  by_cases hd : δ ≤ 1
  · have hb : 1 + 2 / δ ≤ 3 / δ := by
      apply (le_div_iff₀ hδ).mpr
      field_simp
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + 2 / δ) hb
      (finrank ℝ E)
    have h' : (s.card : ℝ) ≤ 3 ^ finrank ℝ E / δ ^ finrank ℝ E :=
      h.trans (by simpa only [div_pow] using hpow)
    have h3 : (0 : ℝ) ≤ 3 ^ finrank ℝ E := by positivity
    calc
      (s.card : ℝ) ≤ 3 ^ finrank ℝ E / δ ^ finrank ℝ E := h'
      _ ≤ 3 ^ finrank ℝ E + 3 ^ finrank ℝ E / δ ^ finrank ℝ E :=
        le_add_of_nonneg_left h3
      _ = 3 ^ finrank ℝ E * (1 + 1 / δ ^ finrank ℝ E) := by ring
  · have hd' : 1 ≤ δ := le_of_lt (lt_of_not_ge hd)
    have hb : 1 + 2 / δ ≤ 3 := by
      have : (2 : ℝ) / δ ≤ 2 := (div_le_iff₀ hδ).mpr (by linarith)
      linarith
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + 2 / δ) hb
      (finrank ℝ E)
    have h' := h.trans hpow
    have h3 : (0 : ℝ) ≤ 3 ^ finrank ℝ E := by positivity
    have hdiv : 0 ≤ 1 / δ ^ finrank ℝ E := by positivity
    nlinarith

end WaringSiegel
