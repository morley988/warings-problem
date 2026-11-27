import WaringLinear.PrimeWindowBounds

/-! # The exact limiting mass from the prime number theorem -/
noncomputable section
namespace WaringLinear.PrimeWindow
open MeasureTheory Filter Set
open scoped Interval Topology
theorem interval_bounds {x y L U : ℝ} (hx₁ : 1<x) (hy : x≤y)
    (hc : ∀ t : ℝ, x≤t → L*t/Real.log t≤count t ∧ count t≤U*t/Real.log t) :
    L*(Real.log (Real.log y)-Real.log (Real.log x))-U/Real.log x ≤ mass x y ∧
    mass x y ≤ U*(Real.log (Real.log y)-Real.log (Real.log x))+U/Real.log y := by
  have hx₀ := zero_lt_one.trans hx₁
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2 (count_integrable hx₀ hy)
  have hkernel : IntervalIntegrable (fun t : ℝ => 1/(t*Real.log t)) volume x y := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hy]
    exact reciprocal_log_continuous hx₁
  have bounds (t : ℝ) (ht : x≤t) :
      L/(t*Real.log t)≤count t/t^2 ∧ count t/t^2≤U/(t*Real.log t) := by
    obtain ⟨hL,hU⟩ := hc t ht
    have ht' : 0<t := by linarith
    have hlog : 0<Real.log t := Real.log_pos (by linarith)
    constructor
    · calc
        _ = (L*t/Real.log t)/t^2 := by field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hL (sq_nonneg _)
    · calc
        _ ≤ (U*t/Real.log t)/t^2 := div_le_div_of_nonneg_right hU (sq_nonneg _)
        _ = _ := by field_simp
  have endpoint (t : ℝ) (ht : x≤t) : 0≤count t/t ∧ count t/t≤U/Real.log t := by
    have h := (hc t ht).2
    have ht' : 0<t := by linarith
    refine ⟨div_nonneg (Nat.cast_nonneg _) ht'.le,?_⟩
    calc
      _ ≤ (U*t/Real.log t)/t := div_le_div_of_nonneg_right h ht'.le
      _ = _ := by field_simp
  have integL := intervalIntegral.integral_mono_on hy (hkernel.const_mul L) hi
    (fun t ht => by simpa only [mul_one_div] using (bounds t ht.1).1)
  have integU := intervalIntegral.integral_mono_on hy hi (hkernel.const_mul U)
    (fun t ht => by simpa only [mul_one_div] using (bounds t ht.1).2)
  rw [intervalIntegral.integral_const_mul,kernel_integral hx₁ hy] at integL integU
  obtain ⟨ex₀,ex₁⟩ := endpoint x le_rfl
  obtain ⟨ey₀,ey₁⟩ := endpoint y hy
  rw [abel hx₀ hy]
  constructor <;> linarith


def CountingAsymptotic : Prop :=
  ∀ δ : ℝ, 0<δ → ∀ᶠ t : ℝ in atTop,
    (1-δ)*t/Real.log t ≤ count t ∧ count t ≤ (1+δ)*t/Real.log t

theorem power_window_limit (pnt : CountingAsymptotic) (v γ : ℝ) (hv : 0<v) (hγ : 1<γ) :
    Tendsto (fun P : ℝ => mass (P^v) (P^(γ*v))) atTop (𝓝 (Real.log γ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hγ₀ := zero_lt_one.trans hγ
  have gl := Real.log_pos hγ
  let δ := ε/(4*Real.log γ)
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) gl)
  have hprod : δ*Real.log γ=ε/4 := by unfold δ;field_simp <;> ring
  obtain ⟨A,hA⟩ := eventually_atTop.1 (pnt δ hδ)
  have dx : Tendsto (fun P : ℝ => (1+δ)/Real.log (P^v)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop hv))
  have dy : Tendsto (fun P : ℝ => (1+δ)/Real.log (P^(γ*v))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (mul_pos hγ₀ hv)))
  filter_upwards [eventually_gt_atTop (1:ℝ), (tendsto_rpow_atTop hv).eventually_ge_atTop A,
    dx.eventually_lt_const (half_pos hε),dy.eventually_lt_const (half_pos hε)] with P hP ha ex ey
  have vx := Real.one_lt_rpow hP hv
  have hvγ : v≤γ*v := by nlinarith only [mul_pos (sub_pos.mpr hγ) hv]
  have hm := interval_bounds vx (Real.rpow_le_rpow_of_exponent_le hP.le hvγ)
    (fun t ht => hA t (ha.trans ht))
  have lp := Real.log_pos hP
  have hP₀ := zero_lt_one.trans hP
  have hid : Real.log (Real.log (P^(γ*v)))-Real.log (Real.log (P^v))=Real.log γ := by
    rw [Real.log_rpow hP₀,Real.log_rpow hP₀,mul_assoc,Real.log_mul hγ₀.ne' (mul_pos hv lp).ne']
    ring
  rw [hid] at hm
  rw [Real.dist_eq,abs_lt]
  constructor <;> nlinarith only [hm.1,hm.2,hprod,ex,ey,hε]

#print axioms power_window_limit
end WaringLinear.PrimeWindow
