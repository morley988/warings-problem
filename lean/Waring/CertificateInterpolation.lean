import Waring.CertificateSoundness
import Waring.SmoothInterpolation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Semantic soundness of the certificate's moment interpolation

Acceptance of an interpolation witness now implies admissibility of each
selected value, provided the raw input values are admissible in the actual
smooth-Weyl-sum sense. No seed or efficient-differencing estimate is assumed
implicitly: the admissibility of raw values is an explicit hypothesis.
-/

noncomputable section

namespace Waring.Certificate

open Waring.SmoothMoments

/-- Analytic meaning of a finite rational curve indexed by half-order. -/
def AdmissibleCurve (k : ℕ) (raw : Curve) : Prop :=
  ∀ i : ℕ, i < raw.size → AdmissibleExponent k (2 * i) (raw[i]! : ℝ)

/-- A proper rational chord has the analytic meaning expected by the checker. -/
theorem admissible_rational_chord {k a i b : ℕ} {x y : Q}
    (hai : a ≤ i) (hib : i ≤ b) (hab : a < b)
    (hx : AdmissibleExponent k (2 * a) (x : ℝ))
    (hy : AdmissibleExponent k (2 * b) (y : ℝ)) :
    AdmissibleExponent k (2 * i)
      (((q (b-i) * x + q (i-a) * y) / q (b-a) : Q) : ℝ) := by
  let t : ℝ := (b-i : ℕ) / (b-a : ℕ)
  have hd : (0 : ℝ) < (b-a : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hab
  have ht₀ : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hd.le
  have ht₁ : t ≤ 1 := (div_le_one hd).mpr (by exact_mod_cast Nat.sub_le_sub_left hai b)
  have hd' : (b : ℝ) - a ≠ 0 := by
    have h : (a : ℝ) < b := by exact_mod_cast hab
    exact ne_of_gt (sub_pos.mpr h)
  have horder : ((2 * i : ℕ) : ℝ) =
      ((2 * a : ℕ) : ℝ) * t + ((2 * b : ℕ) : ℝ) * (1-t) := by
    dsimp [t]
    push_cast
    rw [Nat.cast_sub hib, Nat.cast_sub hab.le]
    field_simp
    ring
  have hvalue :
      (((q (b-i) * x + q (i-a) * y) / q (b-a) : Q) : ℝ) =
        (x : ℝ) * t + (y : ℝ) * (1-t) := by
    dsimp [q, t]
    push_cast
    rw [Nat.cast_sub hib, Nat.cast_sub hai, Nat.cast_sub hab.le]
    field_simp
    ring
  rw [hvalue]
  exact admissibleExponent_interpolation hx hy ht₀ ht₁ horder

/-- Every accepted selected moment is admissible when its input curve is. -/
theorem checkedInterpolation_admissible_at (k : ℕ) (raw : Curve)
    (c : InterpolatedCurve) (h : checkInterpolation raw c = true)
    (hraw : AdmissibleCurve k raw) (i : ℕ) (hi : i < raw.size) :
    AdmissibleExponent k (2 * i) (c.values[i]! : ℝ) := by
  let a := c.witnesses[i]!.1
  let b := c.witnesses[i]!.2
  have hc := checkedInterpolation_chord raw c h i hi
  change a ≤ i ∧ i ≤ b ∧ b < raw.size ∧
    c.values[i]! = (if a == b then raw[a]!
      else (q (b-i)*raw[a]! + q (i-a)*raw[b]!)/q (b-a)) at hc
  rcases hc with ⟨hai, hib, hbn, hv⟩
  have han : a < raw.size := (hai.trans hib).trans_lt hbn
  by_cases hab : a = b
  · have hai' : a = i := Nat.le_antisymm hai (hab ▸ hib)
    have hv' : c.values[i]! = raw[a]! := by simpa [hab] using hv
    rw [hv']
    simpa only [hai'] using hraw a han
  · have hab' : a < b := lt_of_le_of_ne (hai.trans hib) hab
    have hv' : c.values[i]! =
        (q (b-i)*raw[a]! + q (i-a)*raw[b]!)/q (b-a) := by simpa [hab] using hv
    rw [hv']
    exact admissible_rational_chord hai hib hab' (hraw a han) (hraw b hbn)

/-- The checker's entire interpolated curve preserves semantic admissibility. -/
theorem checkedInterpolation_admissible (k : ℕ) (raw : Curve)
    (c : InterpolatedCurve) (h : checkInterpolation raw c = true)
    (hraw : AdmissibleCurve k raw) : AdmissibleCurve k c.values := by
  intro i hi
  have hs := (checkInterpolation_sound raw c h).1
  exact checkedInterpolation_admissible_at k raw c h hraw i (hs ▸ hi)

/-- The explicit upward-rounding inequality preserves admissibility. -/
theorem checkedRounding_admissible {k p : ℕ} {raw rounded : Q}
    (hraw : AdmissibleExponent k p (raw : ℝ))
    (hround : checkRounding raw rounded = true) :
    AdmissibleExponent k p (rounded : ℝ) := by
  have hle : raw ≤ rounded := by
    simp only [checkRounding, Bool.and_eq_true, decide_eq_true_eq] at hround
    exact hround.1.1
  exact admissibleExponent_mono hraw (by exact_mod_cast hle)

#print axioms checkedInterpolation_admissible
#print axioms checkedRounding_admissible

end Waring.Certificate
