import WaringSiegel.WSL3PoissonMixedKMajor

/-! # Actual K(d), with the major fourth moment left visible

The minor estimate is unconditional. The major contribution is reduced to
the literal major fourth moment, whose separate arithmetic estimate is still
needed. The formulas below do not add a hypothesis supplying that estimate.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def mixedKIntegral (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) : ℝ :=
  ∫ q, ‖compactTraceNonzeroCubicSum u huc H hH (traceTorusMul d q)‖ *
      ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 ∂traceHaar

theorem mixedKIntegral_nonneg (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) :
    0 ≤ mixedKIntegral u v huc hvc H R hH hR d :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))

theorem mixedKIntegral_eq_major_add_minor (u v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (H R : ℝ) (hH : 0 < H) (hR : R ≠ 0) (d : 𝓞 K) :
    mixedKIntegral u v huc hvc H R hH.ne' hR d =
      mixedKMajorIntegral u v huc hvc H R hH.ne' hR d +
        mixedKMinorIntegral u v huc hvc H R hH.ne' hR d := by
  let f : ArchimedeanTraceTorus K → ℝ := fun q =>
    ‖compactTraceNonzeroCubicSum u huc H hH.ne' (traceTorusMul d q)‖ *
      ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4
  have hc : Continuous f :=
    (((compactTraceNonzeroCubicSum_continuous _ _ _ _).comp (traceTorusMul_continuous d)).norm).mul
      (((compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous 4)).norm.pow 4)
  have hi : Integrable f traceHaar := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : MeasurableSet ((traceTorusMul d) ⁻¹' nonzeroCubicMajorArcs (K:=K) H) :=
    (traceMajorArcUnion_measurableSet _ _ (by positivity)).preimage (traceTorusMul_continuous d).measurable
  exact (integral_add_compl hs hi).symm

/-- The major reduction after inserting the actual fourth and eighth Hua
moments, still displaying the actual major fourth integral of E_H. -/
theorem mixedKMajorIntegral_volume_bound {u v : mixedSpace K → ℂ}
    (huc : HasCompactSupport u) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H R : ℝ) (hH : 0 < H) (hR : 1 ≤ R),
      ∀ (d : 𝓞 K), d ≠ 0 →
      mixedKMajorIntegral u v huc hvc H R hH.ne' (by linarith) d ≤
        C*(nonzeroCubicMajorFourth u huc H hH.ne')^((1:ℝ)/4)*
          (R^finrank ℚ K : ℝ)^((9:ℝ)/4+ε) := by
  let δ := 4*ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C4,hC4,h4⟩ := compactTraceCubicSum_mul_fourth_moment hv hvc hvs hδ
  obtain ⟨C8,hC8,h8⟩ := compactTraceCubicSum_mul_eighth_moment hv hvc hvs hδ
  refine ⟨(C8*C4^2)^((1:ℝ)/4),by positivity,fun H R hH hR d hd => ?_⟩
  have hR0 : 0 < R := by linarith
  let Z := R^finrank ℚ K
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let A := nonzeroCubicMajorFourth u huc H hH.ne'
  have hA : 0 ≤ A := nonzeroCubicMajorFourth_nonneg _ _ _ _
  have hb := mixedKMajorIntegral_fourth_bound u v huc hvc H R hH hR0.ne' d hd
  have hi4 : 0 ≤ ∫ q, ‖compactTraceWeylSum 3 v hvc R hR0.ne' (traceTorusMul 4 q)‖^4 ∂traceHaar :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hi8 : 0 ≤ ∫ q, ‖compactTraceWeylSum 3 v hvc R hR0.ne' (traceTorusMul 4 q)‖^8 ∂traceHaar :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hb' : mixedKMajorIntegral u v huc hvc H R hH.ne' hR0.ne' d ^4 ≤
      A*(C8*Z^(5+δ))*(C4*Z^(2+δ))^2 := by
    apply hb.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (h8 R hR 4 (by norm_num)) hA)
      (pow_le_pow_left₀ hi4 (h4 R hR 4 (by norm_num)) 2) (sq_nonneg _)
      (mul_nonneg hA (by positivity))
  have hz2 : (Z^(2+δ))^2 = Z^(4+2*δ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hZ.le]
    congr 1
    norm_num
    ring
  have he : A*(C8*Z^(5+δ))*(C4*Z^(2+δ))^2 = (C8*C4^2)*A*Z^(9+3*δ) := by
    rw [mul_pow,hz2]
    calc
      _ = (C8*C4^2)*A*(Z^(5+δ)*Z^(4+2*δ)) := by ring
      _ = _ := by rw [← Real.rpow_add hZ]; congr 2 <;> ring
  rw [he] at hb'
  have hr : mixedKMajorIntegral u v huc hvc H R hH.ne' hR0.ne' d ≤
      ((C8*C4^2)*A*Z^(9+3*δ))^((1:ℝ)/4) := by
    rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos (mixedKMajorIntegral_nonneg _ _ _ _ _ _ _ _ _)
      (by positivity) (by norm_num : (0:ℝ)<4)).mpr
    simpa only [Real.rpow_ofNat] using hb'
  apply hr.trans_eq
  rw [Real.mul_rpow (mul_nonneg (by positivity) hA) (Real.rpow_nonneg hZ.le _),
    Real.mul_rpow (by positivity : 0 ≤ C8*C4^2) hA,← Real.rpow_mul hZ.le]
  congr 2
  dsimp [δ]
  ring

end WaringSiegel.WSL3Poisson
