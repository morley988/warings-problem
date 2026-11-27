import WaringLinear.PrimeWindow
import WaringLinear.PrimeCountingChebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform positive mass in every fixed marked prime window -/
noncomputable section
namespace WaringLinear.PrimeWindow
open MeasureTheory Filter Set
open scoped Interval Topology

def lower : ℝ := Real.log 2/6
def upper : ℝ := 4+4*Real.log 4

theorem positive_constants : 0<lower ∧ 0<upper := by
  constructor
  · unfold lower;positivity
  · unfold upper;positivity

theorem estimates {x y : ℝ} (hx : 9≤x) (hy : x≤y) :
    lower*(Real.log (Real.log y)-Real.log (Real.log x))-upper/Real.log x ≤ mass x y ∧
    mass x y ≤ upper*(Real.log (Real.log y)-Real.log (Real.log x))+upper/Real.log y := by
  have hx₁ : 1<x := by linarith
  have hx₀ := zero_lt_one.trans hx₁
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2 (count_integrable hx₀ hy)
  have hkernel : IntervalIntegrable (fun t : ℝ => 1/(t*Real.log t)) volume x y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    exact reciprocal_log_continuous hx₁
  have bounds (t : ℝ) (ht : 9≤t) :
      lower/(t*Real.log t)≤count t/t^2 ∧ count t/t^2≤upper/(t*Real.log t) := by
    obtain ⟨hL,hU⟩ := PrimeCountingChebyshev.primeCounting_div_bounds t ht
    have ht' : 0<t := by linarith
    have hlog : 0<Real.log t := Real.log_pos (by linarith)
    unfold count lower upper
    constructor
    · calc
        _ = ((Real.log 2/6)*t/Real.log t)/t^2 := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hL (sq_nonneg _)
    · calc
        _ ≤ ((4+4*Real.log 4)*t/Real.log t)/t^2 := div_le_div_of_nonneg_right hU (sq_nonneg _)
        _ = _ := by field_simp
  have endpoint (t : ℝ) (ht : 9≤t) : 0≤count t/t ∧ count t/t≤upper/Real.log t := by
    have h := (PrimeCountingChebyshev.primeCounting_div_bounds t ht).2
    have ht' : 0<t := by linarith
    refine ⟨div_nonneg (Nat.cast_nonneg _) ht'.le,?_⟩
    calc
      _ ≤ (upper*t/Real.log t)/t := div_le_div_of_nonneg_right h ht'.le
      _ = _ := by field_simp
  have hL := intervalIntegral.integral_mono_on hy (hkernel.const_mul lower) hi
    (fun t ht => by simpa only [mul_one_div] using (bounds t (hx.trans ht.1)).1)
  have hU := intervalIntegral.integral_mono_on hy hi (hkernel.const_mul upper)
    (fun t ht => by simpa only [mul_one_div] using (bounds t (hx.trans ht.1)).2)
  rw [intervalIntegral.integral_const_mul,kernel_integral hx₁ hy] at hL hU
  obtain ⟨ex₀,ex₁⟩ := endpoint x hx
  obtain ⟨ey₀,ey₁⟩ := endpoint y (hx.trans hy)
  rw [abel hx₀ hy]
  constructor <;> linarith

/-- With exponent window (v,γv], the lower and upper constants are
independent of v, including when different marked windows are multiplied. -/
theorem power_window_bounds (v γ : ℝ) (hv : 0<v) (hγ : 1<γ) :
    ∀ᶠ P : ℝ in atTop,
      (lower/2)*Real.log γ≤mass (P^v) (P^(γ*v)) ∧
      mass (P^v) (P^(γ*v))≤2*upper*Real.log γ := by
  have L := positive_constants.1
  have U := positive_constants.2
  have hγ₀ := zero_lt_one.trans hγ
  have gl := Real.log_pos hγ
  have divlimit : Tendsto (fun P : ℝ => upper/Real.log (P^v)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hv))
  have divlimit' : Tendsto (fun P : ℝ => upper/Real.log (P^(γ*v))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (mul_pos hγ₀ hv)))
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hv).eventually_ge_atTop 9,
    divlimit.eventually_lt_const (show 0<(lower/2)*Real.log γ by positivity),
    divlimit'.eventually_lt_const (mul_pos U gl)] with P hP hx e₁ e₂
  have hvγ : v≤γ*v := by nlinarith only [mul_pos (sub_pos.mpr hγ) hv]
  have hm := estimates hx (Real.rpow_le_rpow_of_exponent_le hP.le hvγ)
  have hP₀ := zero_lt_one.trans hP
  have lp := Real.log_pos hP
  have hid : Real.log (Real.log (P^(γ*v)))-Real.log (Real.log (P^v))=Real.log γ := by
    rw [Real.log_rpow hP₀,Real.log_rpow hP₀,mul_assoc,
      Real.log_mul hγ₀.ne' (mul_pos hv lp).ne']
    ring
  rw [hid] at hm
  constructor <;> linarith [hm.1,hm.2]

#print axioms estimates
#print axioms power_window_bounds
end WaringLinear.PrimeWindow
