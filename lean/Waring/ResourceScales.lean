import Waring.CubicSamplingAsymptotic
import Mathlib.Tactic.GCongr

/-!
# From the proved sampling shape to the four affine resource caps

These are inequalities at actual positive scales. The scale hypotheses are
displayed, so rounding, smoothness losses, and block support still have to be
accounted for when applying them to a full efficient-differencing policy.
-/

noncomputable section
namespace Waring.ResourceScales
open Waring.RationalHeight Waring.CubicCoefficientSampling

def fourCap (h n j ell : ℝ) : ℝ :=
  min n (min j (min ((n+j-3*h)/2) (ell-2*h)))

theorem sqrt_rpow {P : ℝ} (hP : 0 ≤ P) (x : ℝ) :
    Real.sqrt (P^x) = P^(x/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP]
  congr 1
  ring

/-- The exact four caps in the refined sampling estimate, with each actual
integer scale allowed to satisfy an inequality rather than an exact power law. -/
theorem samplingShape_le_four_rpow {P h n j ell α : ℝ} {H N J : ℕ}
    (hP : 1 ≤ P) (hN : 0 < N) (hJ : 0 < J)
    (hHscale : (H:ℝ) ≤ P^h) (hNscale : P^n ≤ N) (hJscale : P^j ≤ J)
    (hLscale : P^ell ≤ height ((H:ℝ)^3*((N:ℝ)*J)) α) :
    samplingShape H N J α ≤ 4*P^(-fourCap h n j ell) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  let L := height ((H:ℝ)^3*((N:ℝ)*J)) α
  have hL : 0 < L := height_pos _ _
  have h1 : 1/(N:ℝ) ≤ P^(-n) := by
    rw [Real.rpow_neg hP0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hNscale
  have h2 : 1/(J:ℝ) ≤ P^(-j) := by
    rw [Real.rpow_neg hP0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hJscale
  have hnum : Real.sqrt ((H:ℝ)^3) ≤ P^(3*h/2) := by
    calc
      _ ≤ Real.sqrt ((P^h)^3) := Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hHscale 3)
      _ = Real.sqrt (P^(h*3)) := by congr 1; simpa using (Real.rpow_mul_natCast hP0 h 3).symm
      _ = _ := by rw [sqrt_rpow hP0]; congr 1; ring
  have hden : P^((n+j)/2) ≤ Real.sqrt ((N:ℝ)*J) := by
    rw [← sqrt_rpow hP0, Real.rpow_add hPpos]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul hNscale hJscale (Real.rpow_nonneg hP0 _) hNr.le
  have h3 : Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J) ≤ P^(-((n+j-3*h)/2)) := by
    calc
      _ ≤ P^(3*h/2)/P^((n+j)/2) :=
        div_le_div₀ (Real.rpow_nonneg hP0 _) hnum (Real.rpow_pos_of_pos hPpos _) hden
      _ = P^(3*h/2-(n+j)/2) := (Real.rpow_sub hPpos _ _).symm
      _ = _ := by congr 1; ring
  have h4 : (H:ℝ)^2/L ≤ P^(-(ell-2*h)) := by
    calc
      _ ≤ (P^h)^2/P^ell := div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) hHscale 2) (Real.rpow_pos_of_pos hPpos _) hLscale
      _ = P^(h*2)/P^ell := by congr 1; simpa using (Real.rpow_mul_natCast hP0 h 2).symm
      _ = P^(h*2-ell) := (Real.rpow_sub hPpos _ _).symm
      _ = _ := by congr 1; ring
  have hn : fourCap h n j ell ≤ n := min_le_left _ _
  have hj : fourCap h n j ell ≤ j := (min_le_right _ _).trans (min_le_left _ _)
  have hc : fourCap h n j ell ≤ (n+j-3*h)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl : fourCap h n j ell ≤ ell-2*h :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have b1 := h1.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hn))
  have b2 := h2.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hj))
  have b3 := h3.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hc))
  have b4 := h4.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hl))
  unfold samplingShape
  change 1/(N:ℝ)+1/(J:ℝ)+Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+(H:ℝ)^2/L ≤ _
  linarith

/-- Physical conductor identity, valid for both degrees eight and nine. -/
theorem coefficient_conductor_identity (k T f : ℝ) :
    3*(1-k*f)+(2*k*f)+(k-3-k*T+k*f) = k*(1-T) := by ring

/-- The four physical scale caps are precisely the four affine expressions
used by the refined coefficient resource in the exact certificate. -/
theorem fourCap_coefficient_identity (k T f ell : ℝ) :
    fourCap (1-k*f) (2*k*f) (k-3-k*T+k*f) ell =
      min (2*k*f) (min (k-3-k*T+k*f)
        (min ((k-6-k*T+6*k*f)/2) (ell-2+2*k*f))) := by
  unfold fourCap
  congr 3 <;> ring

theorem refined_coefficient_shape {P k T f ell α : ℝ} {H N J : ℕ}
    (hP : 1 ≤ P) (hN : 0 < N) (hJ : 0 < J)
    (hHscale : (H:ℝ) ≤ P^(1-k*f)) (hNscale : P^(2*k*f) ≤ N)
    (hJscale : P^(k-3-k*T+k*f) ≤ J)
    (hLscale : P^ell ≤ height ((H:ℝ)^3*((N:ℝ)*J)) α) :
    samplingShape H N J α ≤ 4*P^(-min (2*k*f)
      (min (k-3-k*T+k*f) (min ((k-6-k*T+6*k*f)/2) (ell-2+2*k*f)))) := by
  simpa only [fourCap_coefficient_identity] using
    samplingShape_le_four_rpow hP hN hJ hHscale hNscale hJscale hLscale

#print axioms samplingShape_le_four_rpow
#print axioms refined_coefficient_shape

end Waring.ResourceScales
