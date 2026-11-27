import WaringSiegel.WSL3UnitComplexSaddle

/-!
# Full complex-place cubic stationary bound for an annular smooth source

Both complex critical points are treated, including arbitrary linear
twists and uniformity in all coefficient directions. Small critical
points lie outside the source; large ones are handled by linear tails.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

def complexSourceAnnulus (rho R : ℝ) : Set ℂ := closedBall 0 R ∩ {z | rho ≤ ‖z‖}

theorem complexSourceAnnulus_isCompact (rho R : ℝ) : IsCompact (complexSourceAnnulus rho R) :=
  (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)

theorem uniform_complex_small_critical_bound {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    {rho R : ℝ} (hrho : 0 < rho) (hWs : support W ⊆ complexSourceAnnulus rho R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℂ, ‖a‖ ≤ rho/2 → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖∫ z, W z*scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ ≤ C := by
  let T : Set (ℂ × ℂ) := closedBall 0 (rho/2) ×ˢ sphere 0 1
  let F : (ℂ × ℂ) × ℂ → ℂ := fun q => W q.2
  let H : (ℂ × ℂ) × ℂ → ℂ := fun q => 3*q.1.2*q.2^2+(-3*q.1.2*q.1.1^2)
  have hH : ContDiff ℝ ∞ H := by fun_prop
  have hgap : ∀ p ∈ T, ∀ z ∈ tsupport (fun y => F (p,y)), rho^2 ≤ ‖H (p,z)‖ := by
    intro p hp z hz
    have ha : ‖p.1‖ ≤ rho/2 := by simpa only [mem_closedBall,dist_zero_right] using hp.1
    have ht : ‖p.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.2
    have hz' := (closure_minimal hWs (complexSourceAnnulus_isCompact rho R).isClosed) hz
    have hzr : rho ≤ ‖z‖ := hz'.2
    have he : H (p,z) = 3*p.2*(z^2-p.1^2) := by dsimp only [H]; ring
    rw [he,norm_mul,norm_mul,ht]
    norm_num
    have htri := norm_sub_le (z^2-p.1^2) (-p.1^2)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_pow] at htri
    have hza : (rho/2)^2 ≥ ‖p.1‖^2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hzz := pow_le_pow_left₀ hrho.le hzr 2
    nlinarith
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound
    (hW.comp contDiff_snd) hH
    ((isCompact_closedBall 0 (rho/2)).prod (isCompact_sphere 0 1))
    (complexSourceAnnulus_isCompact rho R) (fun _ => hWs)
    (phi := fun p => complexSaddlePhase p.1 p.2)
    (fun p _ => complexSaddlePhase_contDiff p.1 p.2)
    (fun p _ z => complex_cubic_gradient_real p.2 (-3*p.2*p.1^2) z)
    (fun p _ z => complex_cubic_gradient_imag p.2 (-3*p.2*p.1^2) z)
    (sq_pos_of_pos hrho) hgap 1
  refine ⟨C,hC,fun a t ha ht lambda hl => ?_⟩
  have hp : (a,t) ∈ T := by
    constructor
    · simpa only [mem_closedBall,dist_zero_right] using ha
    · simpa only [mem_sphere,dist_zero_right] using ht
  simpa only [pow_one,abs_of_pos hl] using hb (a,t) hp lambda

theorem complexCubicOscillatoryIntegral_saddle (W : ℂ → ℂ) {theta u : ℂ}
    (htheta : theta ≠ 0) {a : ℂ} (ha : a^2 = -u/(3*theta)) :
    complexCubicOscillatoryIntegral W theta u =
      ∫ z, W z*scalarOscillatoryPhase ‖theta‖
        (complexSaddlePhase a (theta/(‖theta‖:ℂ))) z := by
  have hn : (‖theta‖:ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr htheta)
  have hu : u = -3*theta*a^2 := by rw [ha]; field_simp
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  unfold scalarOscillatoryPhase complexSaddlePhase
  congr 1
  have he : theta*z^3+u*z = (‖theta‖:ℂ)*
      ((theta/(‖theta‖:ℂ))*z^3+(-3*(theta/(‖theta‖:ℂ))*a^2)*z) := by
    rw [hu]
    field_simp
  rw [he,Complex.re_ofReal_mul]
  push_cast
  ring

theorem complexCubicOscillatoryIntegral_norm_le {W : ℂ → ℂ} {R : ℝ}
    (hWs : support W ⊆ closedBall 0 R) (hWnorm : ∀ z, ‖W z‖ ≤ 1) (theta u : ℂ) :
    ‖complexCubicOscillatoryIntegral W theta u‖ ≤ volume.real (closedBall (0:ℂ) R) := by
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 R)
  · intro z hz
    apply hWs
    intro hzero
    apply hz
    simp only [hzero,zero_mul]
  · intro z
    have he : ‖Complex.exp (Complex.I*(2*(theta*z^3+u*z).re : ℝ))‖ = 1 := by
      simpa only [scalarOscillatoryPhase,Complex.ofReal_one,one_mul] using
        scalarOscillatoryPhase_norm 1 (fun y : ℂ => 2*(theta*y^3+u*y).re) z
    rw [norm_mul,he,mul_one]
    exact hWnorm z

/-- Uniform two-dimensional stationary cancellation for every smooth
unit-bounded source supported in a fixed annulus away from zero. -/
theorem complex_cubic_stationary_bound {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    (hWnorm : ∀ z, ‖W z‖ ≤ 1) {rho R : ℝ} (hrho : 0 < rho) (hR : 0 ≤ R)
    (hWs : support W ⊆ complexSourceAnnulus rho R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      (1+‖theta‖)*‖complexCubicOscillatoryIntegral W theta u‖ ≤ C := by
  let eta := cubicTailRadius R
  let A := 1+eta⁻¹
  have heta : 0 < eta := cubicTailRadius_pos R
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    linarith [(inv_pos.mpr heta).le]
  have hetaA : 1 ≤ eta*A := by
    dsimp only [A]
    rw [mul_add,mul_one,mul_inv_cancel₀ heta.ne']
    linarith
  have hball : support W ⊆ closedBall 0 R := fun z hz => (hWs hz).1
  obtain ⟨Cs,hCs,hsmall⟩ := uniform_complex_small_critical_bound hW hrho hWs
  obtain ⟨Cm,hCm,hmedium⟩ := uniform_complex_saddle_stationary_bound (A := A) hW hWnorm
    (complexSourceAnnulus_isCompact rho R) hWs (by positivity : 0 < rho/2)
  obtain ⟨Cl,hCl,hlarge⟩ := complex_cubic_nonstationary_bound hW hR hball 1
  let V := volume.real (closedBall (0:ℂ) R)
  refine ⟨2*(Cs+Cm+Cl+V+1),by dsimp only [V]; positivity,fun theta u => ?_⟩
  have htriv := complexCubicOscillatoryIntegral_norm_le hball hWnorm theta u
  by_cases hsmalltheta : ‖theta‖ ≤ 1
  · have hV : 0 ≤ V := measureReal_nonneg
    change (1+‖theta‖)*‖complexCubicOscillatoryIntegral W theta u‖ ≤ _
    dsimp only [V] at *
    nlinarith [norm_nonneg (complexCubicOscillatoryIntegral W theta u),norm_nonneg theta]
  have ht : 1 < ‖theta‖ := lt_of_not_ge hsmalltheta
  have htheta : theta ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one ht))
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (-u/(3*theta)) (by norm_num : 0 < (2:ℕ))
  let t := theta/(‖theta‖:ℂ)
  have htt : ‖t‖ = 1 := by
    dsimp only [t]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg theta),
      div_self (norm_ne_zero_iff.mpr htheta)]
  have he := complexCubicOscillatoryIntegral_saddle W htheta ha
  have hmain : ‖theta‖*‖complexCubicOscillatoryIntegral W theta u‖ ≤ Cs+Cm+Cl := by
    by_cases hsa : ‖a‖ ≤ rho/2
    · rw [he]
      have h := hsmall a t hsa htt ‖theta‖ (lt_trans zero_lt_one ht)
      dsimp only [t] at h
      linarith
    by_cases hma : ‖a‖ ≤ A
    · rw [he]
      have h := hmedium a t (le_of_lt (lt_of_not_ge hsa)) hma htt ‖theta‖ (lt_trans zero_lt_one ht)
      dsimp only [t] at h
      linarith
    have haa : A ≤ ‖a‖ := le_of_lt (lt_of_not_ge hma)
    have ha1 : 1 ≤ ‖a‖ := hA1.trans haa
    have hetaa : 1 ≤ eta*‖a‖ := hetaA.trans (mul_le_mul_of_nonneg_left haa heta.le)
    have ha2 : 1 ≤ ‖a‖^2 := by nlinarith
    have hetaa2 : 1 ≤ eta*‖a‖^2 := by
      have hmul := mul_le_mul_of_nonneg_right hetaa (norm_nonneg a)
      nlinarith
    have hu : u = -3*theta*a^2 := by rw [ha]; field_simp
    have hun : ‖u‖ = 3*‖theta‖*‖a‖^2 := by rw [hu,norm_mul,norm_mul,norm_pow]; norm_num
    have hule : ‖theta‖ ≤ ‖u‖ := by rw [hun]; nlinarith
    have hu1 : 1 ≤ ‖u‖ := (le_of_lt ht).trans hule
    have hregion : ‖theta‖ ≤ cubicTailRadius R*‖u‖ := by
      rw [hun]
      change ‖theta‖ ≤ eta*(3*‖theta‖*‖a‖^2)
      have hm := mul_le_mul_of_nonneg_left hetaa2 (norm_nonneg theta)
      nlinarith
    have h := hlarge theta u hu1 hregion
    rw [pow_one] at h
    have hm := mul_le_mul_of_nonneg_right hule (norm_nonneg (complexCubicOscillatoryIntegral W theta u))
    linarith
  have hV : 0 ≤ V := measureReal_nonneg
  dsimp only [V] at *
  nlinarith

/-- The actual smooth radial place factor, including every linear twist. -/
theorem smooth_complex_cubic_stationary_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      (1+‖theta‖)*‖smoothComplexCubicIntegral rho R theta u‖ ≤ C := by
  apply complex_cubic_stationary_bound
    (Complex.ofRealCLM.contDiff.comp
      ((positiveSmoothWindow_contDiff (rho^2) (R^2)).comp complex_normSq_contDiff))
    (rho := rho/2) (R := 2*R)
  · intro z
    change ‖(positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positiveSmoothWindow_nonneg _ _ _)]
    exact positiveSmoothWindow_le_one _ _ _
  · positivity
  · positivity
  · intro z hz
    have hn : positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) ≠ 0 := by
      intro he
      apply hz
      change (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ) = 0
      rw [he]
      rfl
    have hs := positiveSmoothWindow_support (sq_pos_of_pos hrho) (sq_pos_of_pos hR) hn
    rw [Complex.normSq_eq_norm_sq] at hs
    constructor
    · simp only [mem_closedBall,dist_zero_right]
      nlinarith [norm_nonneg z]
    · change rho/2 ≤ ‖z‖
      nlinarith [norm_nonneg z]

/-- The manuscript's literal 2π trace normalization at a complex place. -/
theorem complexPlaceCubicIntegral_stationary_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      (1+‖theta‖)*‖complexPlaceCubicIntegral rho R theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := smooth_complex_cubic_stationary_bound rho R hrho hR
  refine ⟨C,hC,fun theta u => ?_⟩
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hn : ‖(2*Real.pi:ℂ)*theta‖ = (2*Real.pi)*‖theta‖ := by
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have ht : 1+‖theta‖ ≤ 1+‖(2*Real.pi:ℂ)*theta‖ := by rw [hn]; nlinarith [norm_nonneg theta]
  rw [complexPlaceCubicIntegral_eq_rescaled]
  exact (mul_le_mul_of_nonneg_right ht (norm_nonneg _)).trans (hb _ _)

#print axioms complex_cubic_stationary_bound
#print axioms complexPlaceCubicIntegral_stationary_bound
end WaringSiegel.WSL3
