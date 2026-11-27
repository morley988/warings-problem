import WaringSiegel.WSL3UnitRealCubicTail
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# First-derivative cancellation for arbitrary real cubic linear twists

The reciprocal-variation argument is adapted from the proved classical
Waring module `Waring/EndgameCompletionSingular.lean`, theorem
`norm_integral_le_two_mul_of_reciprocal_deriv`. The new form allows either
sign of the reciprocal, retaining exact cancellation of its total variation.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
namespace WaringSiegel.WSL3
set_option maxHeartbeats 800000

theorem norm_intervalIntegral_le_variation_of_reciprocal
    {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℂ} {g g' : ℝ → ℝ} (C : ℂ)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hf'c : ContinuousOn f' (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b))
    (hg'c : ContinuousOn g' (Set.Icc a b))
    (hfd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hgd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hident : ∀ t ∈ Set.Icc a b, C*(g t : ℂ)*f' t = f t)
    (hfnorm : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ 1)
    (hgneg : ∀ t ∈ Set.Icc a b, g' t ≤ 0) :
    ‖∫ t in a..b, f t‖ ≤ ‖C‖*(|g a|+|g b|+g a-g b) := by
  have hfc' : ContinuousOn f (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hf'c' : ContinuousOn f' (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hgc' : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hg'c' : ContinuousOn g' (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hCgc : ContinuousOn (fun t => C*(g t : ℂ)) (Set.uIcc a b) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hgc')
  have hCg'c : ContinuousOn (fun t => C*(g' t : ℂ)) (Set.uIcc a b) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hg'c')
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t => C*(g t : ℂ)) (u' := fun t => C*(g' t : ℂ))
    (v := f) (v' := f') hCgc hfc'
    (fun t ht => (hgd t (by simpa only [min_eq_left hab, max_eq_right hab] using
      Set.Ioo_subset_Icc_self ht)).ofReal_comp.const_mul C)
    (fun t ht => hfd t (by simpa only [min_eq_left hab, max_eq_right hab] using
      Set.Ioo_subset_Icc_self ht))
    hCg'c.intervalIntegrable hf'c'.intervalIntegrable
  have hid : (∫ t in a..b, C*(g t : ℂ)*f' t) = ∫ t in a..b, f t := by
    apply intervalIntegral.integral_congr
    simpa only [Set.uIcc_of_le hab] using hident
  rw [hid] at hibp
  have hFTC : (∫ t in a..b, g' t) = g b-g a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hg'c'.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hgd
  have hint : ‖∫ t in a..b, C*(g' t : ℂ)*f t‖ ≤ ‖C‖*(g a-g b) := by
    calc
      _ ≤ ∫ t in a..b, ‖C*(g' t : ℂ)*f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, ‖C‖*(-g' t) := by
        apply intervalIntegral.integral_mono_on hab
          ((hCg'c.mul hfc').norm.intervalIntegrable)
          ((continuousOn_const.mul hg'c'.neg).intervalIntegrable)
        intro t ht
        have hng : 0 ≤ -g' t := neg_nonneg.mpr (hgneg t ht)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (hgneg t ht)]
        exact (mul_le_mul_of_nonneg_left (hfnorm t ht) (by positivity)).trans_eq (mul_one _)
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hFTC]; ring
  have henda : ‖C*(g a : ℂ)*f a‖ ≤ ‖C‖*|g a| := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hfnorm a ⟨le_rfl,hab⟩) (by positivity)).trans_eq (mul_one _)
  have hendb : ‖C*(g b : ℂ)*f b‖ ≤ ‖C‖*|g b| := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hfnorm b ⟨hab,le_rfl⟩) (by positivity)).trans_eq (mul_one _)
  rw [hibp]
  calc
    _ ≤ ‖C*(g b : ℂ)*f b - C*(g a : ℂ)*f a‖ +
        ‖∫ t in a..b, C*(g' t : ℂ)*f t‖ := norm_sub_le _ _
    _ ≤ (‖C‖*|g b|+‖C‖*|g a|)+‖C‖*(g a-g b) :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add hendb henda)) hint
    _ = _ := by ring

/-- The literal unit-modulus real cubic phase, before inserting 2π. -/
def realCubicPhase (theta u x : ℝ) : ℂ :=
  Complex.exp (Complex.I*(theta*x^3+u*x : ℝ))

theorem realCubicPhase_norm (theta u x : ℝ) : ‖realCubicPhase theta u x‖ = 1 := by
  rw [realCubicPhase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

theorem realCubicPhase_contDiff (theta u : ℝ) : ContDiff ℝ ∞ (realCubicPhase theta u) :=
  Complex.contDiff_exp.comp (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_id.pow 3)).add (contDiff_const.mul contDiff_id))))

theorem realCubicPhase_hasDerivAt (theta u x : ℝ) :
    HasDerivAt (realCubicPhase theta u)
      (realCubicPhase theta u x * Complex.I*(3*theta*x^2+u : ℝ)) x := by
  have hq : HasDerivAt (fun y : ℝ => theta*y^3+u*y) (3*theta*x^2+u) x := by
    convert ((hasDerivAt_pow 3 x).const_mul theta).add ((hasDerivAt_id x).const_mul u) using 1 <;>
      norm_num <;> ring
  have h := (hq.ofReal_comp.const_mul Complex.I).cexp
  convert h using 1 <;> simp only [realCubicPhase] <;> ring

theorem realCubicPhase_deriv_continuous (theta u : ℝ) :
    Continuous (fun x => realCubicPhase theta u x*Complex.I*(3*theta*x^2+u : ℝ)) :=
  ((realCubicPhase_contDiff theta u).continuous.mul continuous_const).mul
    (Complex.continuous_ofReal.comp (by fun_prop))

/-- A derivative gap gives actual cancellation, uniformly in both the
linear coefficient and the interval endpoints. -/
theorem real_cubic_first_derivative_bound {a b theta u delta : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (htheta : 0 ≤ theta) (hdelta : 0 < delta)
    (hgap : ∀ x ∈ Set.Icc a b, delta ≤ |3*theta*x^2+u|) :
    ‖∫ x in a..b, realCubicPhase theta u x‖ ≤ 4/delta := by
  let D : ℝ → ℝ := fun x => 3*theta*x^2+u
  let g : ℝ → ℝ := fun x => (D x)⁻¹
  let g' : ℝ → ℝ := fun x => -(6*theta*x)/(D x)^2
  have hD0 (x : ℝ) (hx : x ∈ Set.Icc a b) : D x ≠ 0 :=
    abs_pos.mp (hdelta.trans_le (hgap x hx))
  have hDc : Continuous D := by fun_prop
  have hgc : ContinuousOn g (Set.Icc a b) :=
    hDc.continuousOn.inv₀ hD0
  have hg'c : ContinuousOn g' (Set.Icc a b) :=
    (by fun_prop : Continuous (fun x : ℝ => -(6*theta*x))).continuousOn.div
      (hDc.continuousOn.pow 2) (fun x hx => pow_ne_zero _ (hD0 x hx))
  have hDd (x : ℝ) : HasDerivAt D (6*theta*x) x := by
    convert ((hasDerivAt_pow 2 x).const_mul (3*theta)).add_const u using 1 <;> norm_num <;> ring
  have hgd (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt g (g' x) x :=
    (hDd x).inv (hD0 x hx)
  have hgneg (x : ℝ) (hx : x ∈ Set.Icc a b) : g' x ≤ 0 := by
    dsimp only [g']
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg htheta (ha.trans hx.1)])
      (sq_nonneg _)
  have hid (x : ℝ) (hx : x ∈ Set.Icc a b) :
      Complex.I⁻¹*(g x : ℂ)*(realCubicPhase theta u x*Complex.I*(D x : ℂ)) =
        realCubicPhase theta u x := by
    have hz : (D x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hD0 x hx)
    dsimp only [g]
    rw [Complex.ofReal_inv]
    field_simp
  have hbnd := norm_intervalIntegral_le_variation_of_reciprocal hab Complex.I⁻¹
    (realCubicPhase_contDiff theta u).continuous.continuousOn
    (realCubicPhase_deriv_continuous theta u).continuousOn
    hgc hg'c (fun x _ => realCubicPhase_hasDerivAt theta u x) hgd hid
    (fun x _ => (realCubicPhase_norm theta u x).le) hgneg
  have hga : |g a| ≤ 1/delta := by
    dsimp only [g]
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hdelta (hgap a ⟨le_rfl,hab⟩)
  have hgb : |g b| ≤ 1/delta := by
    dsimp only [g]
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hdelta (hgap b ⟨hab,le_rfl⟩)
  simp only [norm_inv, Complex.norm_I, inv_one, one_mul] at hbnd
  apply hbnd.trans
  rw [show 4/delta = 4*(1/delta) by ring]
  linarith [le_abs_self (g a), neg_le_abs (g b)]

#print axioms real_cubic_first_derivative_bound
end WaringSiegel.WSL3
