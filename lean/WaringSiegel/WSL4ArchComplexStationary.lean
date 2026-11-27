import WaringSiegel.WSL4ArchComplexZeroShells

/-!
# Complex cubic two-thirds decay for sources that include zero

The inner disk has area delta squared, and the outer annuli satisfy the
proved radius-uniform stationary bound. Choosing delta = norm(theta)^(-1/3)
and summing the geometric series proves the sharp dimensional exponent.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1500000

/-- Genuine uniform complex cubic cancellation across the degenerate point. -/
theorem complex_cubic_compact_abs_stationary {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hfnorm : ∀ z, ‖f z‖ ≤ 1) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      ‖theta‖^((2:ℝ)/3) * ‖complexCubicOscillatoryIntegral f theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_zero_shell_bound hf hfnorm hR hfs
  refine ⟨volume.real (closedBall (0:ℂ) 2)+2*C+1,by positivity,fun theta u => ?_⟩
  by_cases ht : theta = 0
  · simp [ht]
    positivity
  have htpos : 0 < ‖theta‖ := norm_pos_iff.mpr ht
  let s : ℝ := ‖theta‖^((1:ℝ)/3)
  let delta : ℝ := s⁻¹
  have hs : 0 < s := Real.rpow_pos_of_pos htpos _
  have hd : 0 < delta := inv_pos.mpr hs
  have hs3 : s^3 = ‖theta‖ := by
    dsimp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    norm_num
  have hs2 : s^2 = ‖theta‖^((2:ℝ)/3) := by
    dsimp only [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    norm_num
  have hdid : s^2*delta^2 = 1 := by
    dsimp only [delta]
    rw [← mul_pow,mul_inv_cancel₀ hs.ne']
    norm_num
  obtain ⟨N,hN⟩ := exists_nat_gt (R/delta)
  have hpow : (N:ℝ) ≤ (2:ℝ)^N := by
    exact_mod_cast (show N < 2^N from Nat.lt_two_pow_self).le
  have hN' : R ≤ (2:ℝ)^N*delta := by
    have hdN := (div_lt_iff₀ hd).mp hN
    exact hdN.le.trans (mul_le_mul_of_nonneg_right hpow hd.le)
  have hdecomp := complexCubicOscillatoryIntegral_dyadic hf.continuous hfs hd theta u hN'
  have hi := complexNearZeroInnerIntegral_bound hfnorm theta u hd
  have hi' : s^2*‖complexNearZeroInnerIntegral f theta u delta‖ ≤
      volume.real (closedBall (0:ℂ) 2) := by
    have h := mul_le_mul_of_nonneg_left hi (sq_nonneg s)
    simpa only [← mul_assoc,hdid,one_mul] using h
  have hshell : ∀ j : ℕ,
      s^2*‖complexNearZeroShellIntegral f theta u ((2:ℝ)^j*delta)‖ ≤ C*(1/2:ℝ)^j := by
    intro j
    have h := hb theta u ((2:ℝ)^j*delta) (by positivity)
    have hp : 0 < (2:ℝ)^j := by positivity
    have he : ‖theta‖*((2:ℝ)^j*delta) = (2:ℝ)^j*s^2 := by
      rw [← hs3]
      dsimp only [delta]
      field_simp
    rw [he,mul_assoc] at h
    have hhalf : (2:ℝ)^j*(1/2:ℝ)^j = 1 := by
      rw [← mul_pow]
      norm_num
    apply (mul_le_mul_left hp).mp
    calc
      _ ≤ C := h
      _ = _ := by rw [← mul_assoc,mul_comm ((2:ℝ)^j) C,mul_assoc,hhalf,mul_one]
  have hn := norm_add_le (complexNearZeroInnerIntegral f theta u delta)
    (∑ j ∈ Finset.range N, complexNearZeroShellIntegral f theta u ((2:ℝ)^j*delta))
  have hsum := norm_sum_le (s := Finset.range N)
    (f := fun j => complexNearZeroShellIntegral f theta u ((2:ℝ)^j*delta))
  have hsum' : s^2*(∑ j ∈ Finset.range N,
      ‖complexNearZeroShellIntegral f theta u ((2:ℝ)^j*delta)‖) ≤ 2*C := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range N, C*(1/2:ℝ)^j := Finset.sum_le_sum (fun j _ => hshell j)
      _ = C*(∑ j ∈ Finset.range N, (1/2:ℝ)^j) := (Finset.mul_sum _ _ _).symm
      _ ≤ C*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hC.le
      _ = _ := by ring
  rw [← hs2,hdecomp]
  nlinarith [sq_nonneg s]

theorem one_add_rpow_two_thirds_le_two {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1+t)^((2:ℝ)/3) ≤ 2 := by
  calc
    _ ≤ (2:ℝ)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = _ := Real.rpow_one _

theorem one_add_rpow_two_thirds_le_mul {t : ℝ} (ht : 1 ≤ t) :
    (1+t)^((2:ℝ)/3) ≤ 2*t^((2:ℝ)/3) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  calc
    _ ≤ (2*t)^((2:ℝ)/3) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = (2:ℝ)^((2:ℝ)/3)*t^((2:ℝ)/3) := Real.mul_rpow (by norm_num) ht0
    _ ≤ 2*t^((2:ℝ)/3) := mul_le_mul_of_nonneg_right
      (by
        calc
          (2:ℝ)^((2:ℝ)/3) ≤ (2:ℝ)^(1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one _) (Real.rpow_nonneg ht0 _)

/-- The full complex-place bound includes bounded theta and arbitrary linear twists. -/
theorem complex_cubic_compact_stationary_bound {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hfnorm : ∀ z, ‖f z‖ ≤ 1) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      (1+‖theta‖)^((2:ℝ)/3) * ‖complexCubicOscillatoryIntegral f theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complex_cubic_compact_abs_stationary hf hfnorm hR hfs
  let V : ℝ := volume.real (closedBall (0:ℂ) R)
  have hV : 0 ≤ V := measureReal_nonneg
  refine ⟨2*C+2*V+1,by positivity,fun theta u => ?_⟩
  by_cases ht : 1 ≤ ‖theta‖
  · have hm := mul_le_mul_of_nonneg_right (one_add_rpow_two_thirds_le_mul ht)
      (norm_nonneg (complexCubicOscillatoryIntegral f theta u))
    have hh := hb theta u
    nlinarith
  · have hm := mul_le_mul
      (one_add_rpow_two_thirds_le_two (norm_nonneg theta) (le_of_not_ge ht))
      (complexCubicOscillatoryIntegral_norm_le hfs hfnorm theta u)
      (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    change (1+‖theta‖)^((2:ℝ)/3)*‖complexCubicOscillatoryIntegral f theta u‖ ≤ 2*V at hm
    linarith

/-- Literal 2 pi times the complex trace phase for a general compact source. -/
def complexCubicTraceIntegral (f : ℂ → ℂ) (theta u : ℂ) : ℂ :=
  complexCubicOscillatoryIntegral f ((2*Real.pi:ℂ)*theta) ((2*Real.pi:ℂ)*u)

theorem complex_cubic_trace_stationary_bound {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hfnorm : ∀ z, ‖f z‖ ≤ 1) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      (1+‖theta‖)^((2:ℝ)/3) * ‖complexCubicTraceIntegral f theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complex_cubic_compact_stationary_bound hf hfnorm hR hfs
  refine ⟨C,hC,fun theta u => ?_⟩
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hn : ‖(2*Real.pi:ℂ)*theta‖ = (2*Real.pi)*‖theta‖ := by
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have ht : 1+‖theta‖ ≤ 1+‖(2*Real.pi:ℂ)*theta‖ := by rw [hn]; nlinarith [norm_nonneg theta]
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by positivity) ht (by positivity : (0:ℝ) ≤ 2/3))
    (norm_nonneg (complexCubicTraceIntegral f theta u))).trans (hb _ _)

#print axioms complex_cubic_compact_stationary_bound
#print axioms complex_cubic_trace_stationary_bound
end WaringSiegel.WSL4

