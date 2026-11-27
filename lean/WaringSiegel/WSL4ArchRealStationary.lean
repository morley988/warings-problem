import WaringSiegel.WSL4ArchRealPrimitive

/-!
# Real cubic stationary bounds for compact amplitudes that may meet zero

The source amplitude is fixed before both frequency coefficients. Arbitrary
smooth compact complex amplitudes are allowed, including a bump equal to one
near zero. The final theorem restores the literal 2 pi convention.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

theorem realCubicOscillatoryIntegral_norm_le_integral (f : ℝ → ℂ) (theta u : ℝ) :
    ‖realCubicOscillatoryIntegral f theta u‖ ≤ ∫ x, ‖f x‖ := by
  change ‖∫ x, f x * realCubicPhase theta u x‖ ≤ _
  calc
    _ ≤ ∫ x, ‖f x * realCubicPhase theta u x‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_mul, realCubicPhase_norm, mul_one]

theorem realCubicOscillatoryIntegral_eq_interval {f : ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hfs : support f ⊆ closedBall 0 R) (theta u : ℝ) :
    realCubicOscillatoryIntegral f theta u =
      ∫ x in (-(R+1))..(R+1), f x * realCubicPhase theta u x := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)).symm
  have hf : f x = 0 := by
    by_contra hn
    have hs := hfs hn
    have hab : |x| ≤ R := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hs
    have hab' := abs_le.mp hab
    exact hx ⟨by linarith, by linarith⟩
  simp only [hf, zero_mul]

/-- Uniform inverse-third-root cancellation before adding the bounded-frequency term. -/
theorem real_cubic_compact_abs_stationary {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      |theta|^((1:ℝ)/3) * ‖realCubicOscillatoryIntegral f theta u‖ ≤ C := by
  obtain ⟨D,hD,hbound⟩ := ((isCompact_Icc : IsCompact (Set.Icc (-(R+1)) (R+1))).image
    (hf.continuous_deriv (by simp))).isBounded.exists_pos_norm_le
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc (-(R+1)) (R+1)) : ‖deriv f x‖ ≤ D :=
    hbound _ (Set.mem_image_of_mem _ hx)
  have hfb : f (R+1) = 0 := by
    by_contra hn
    have hs := hfs hn
    have hab : |R+1| ≤ R := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hs
    rw [abs_of_pos (by linarith : 0 < R+1)] at hab
    linarith
  refine ⟨40*D*(R+1)+1,by positivity,fun theta u => ?_⟩
  by_cases ht : theta = 0
  · simp [ht]
    positivity
  have hs : 0 < |theta|^((1:ℝ)/3) := Real.rpow_pos_of_pos (abs_pos.mpr ht) _
  have hp (x : ℝ) (_hx : x ∈ Set.Icc (-(R+1)) (R+1)) :
      ‖∫ t in (-(R+1))..x, realCubicPhase theta u t‖ ≤ 20/|theta|^((1:ℝ)/3) := by
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using real_cubic_primitive_one_third theta (-(R+1)) x u
  have hi := weighted_interval_bound_of_primitive (by linarith : -(R+1) ≤ R+1)
    hD.le hf (realCubicPhase_contDiff theta u).continuous hfb hderiv hp
  rw [← realCubicOscillatoryIntegral_eq_interval hR hfs] at hi
  have hm := mul_le_mul_of_nonneg_left hi hs.le
  have he : |theta|^((1:ℝ)/3) * (D*(20/|theta|^((1:ℝ)/3))*((R+1)-(-(R+1)))) =
      40*D*(R+1) := by field_simp; ring
  rw [he] at hm
  linarith

theorem one_add_rpow_one_third_le_two {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1+t)^((1:ℝ)/3) ≤ 2 := by
  calc
    _ ≤ (2:ℝ)^((1:ℝ)/3) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ ≤ (2:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = _ := Real.rpow_one _

theorem one_add_rpow_one_third_le_mul {t : ℝ} (ht : 1 ≤ t) :
    (1+t)^((1:ℝ)/3) ≤ 2*t^((1:ℝ)/3) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  calc
    _ ≤ (2*t)^((1:ℝ)/3) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = (2:ℝ)^((1:ℝ)/3)*t^((1:ℝ)/3) := Real.mul_rpow (by norm_num) ht0
    _ ≤ 2*t^((1:ℝ)/3) := mul_le_mul_of_nonneg_right
      (by
        calc
          (2:ℝ)^((1:ℝ)/3) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one _) (Real.rpow_nonneg ht0 _)

/-- Full real-place one-third stationary decay, uniform in every linear twist. -/
theorem real_cubic_compact_stationary_bound {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      (1+|theta|)^((1:ℝ)/3) * ‖realCubicOscillatoryIntegral f theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := real_cubic_compact_abs_stationary hf hR hfs
  let M : ℝ := ∫ x, ‖f x‖
  have hM : 0 ≤ M := integral_nonneg (fun x => norm_nonneg _)
  refine ⟨2*C+2*M+1,by positivity,fun theta u => ?_⟩
  by_cases ht : 1 ≤ |theta|
  · have hm := mul_le_mul_of_nonneg_right (one_add_rpow_one_third_le_mul ht)
      (norm_nonneg (realCubicOscillatoryIntegral f theta u))
    have hh := hb theta u
    nlinarith
  · have hm := mul_le_mul
      (one_add_rpow_one_third_le_two (abs_nonneg theta) (le_of_not_ge ht))
      (realCubicOscillatoryIntegral_norm_le_integral f theta u)
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    change (1+|theta|)^((1:ℝ)/3)*‖realCubicOscillatoryIntegral f theta u‖ ≤ 2*M at hm
    linarith

/-- Literal Fourier normalization for a general real-place compact amplitude. -/
def realCubicTraceIntegral (f : ℝ → ℂ) (theta u : ℝ) : ℂ :=
  realCubicOscillatoryIntegral f (2*Real.pi*theta) (2*Real.pi*u)

theorem real_cubic_trace_stationary_bound {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      (1+|theta|)^((1:ℝ)/3) * ‖realCubicTraceIntegral f theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := real_cubic_compact_stationary_bound hf hR hfs
  refine ⟨C,hC,fun theta u => ?_⟩
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have ht : |theta| ≤ |2*Real.pi*theta| := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith [abs_nonneg theta]
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by positivity) (by linarith : 1+|theta| ≤ 1+|2*Real.pi*theta|)
      (by positivity : (0:ℝ) ≤ 1/3))
    (norm_nonneg (realCubicTraceIntegral f theta u))).trans (hb _ _)

#print axioms real_cubic_compact_stationary_bound
#print axioms real_cubic_trace_stationary_bound
end WaringSiegel.WSL4

