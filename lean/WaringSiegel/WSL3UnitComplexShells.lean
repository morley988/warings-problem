import WaringSiegel.WSL3UnitComplexAnnuli
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Actual affine scaling and shell cancellation for a complex cubic saddle
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

theorem complex_integral_affine (f : ℂ → ℂ) (a : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z, f z) = (r^2:ℝ) • ∫ y : ℂ, f (a+(r:ℂ)*y) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
    (fun z => f (a+z)) r (hR := hr.le)
  simp only [Complex.finrank_real_complex,Complex.real_smul,integral_add_left_eq_self] at h
  rw [h,Complex.real_smul]
  have hn : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp

def complexCenteredCubicPhase (a t z : ℂ) : ℝ :=
  2*(t*((z-a)^3+3*a*(z-a)^2)).re

theorem complexCenteredCubicPhase_contDiff (a t : ℂ) :
    ContDiff ℝ ∞ (complexCenteredCubicPhase a t) :=
  contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul
    (((contDiff_id.sub contDiff_const).pow 3).add
      (contDiff_const.mul ((contDiff_id.sub contDiff_const).pow 2)))))

theorem complexCenteredCubicPhase_scale (a t y : ℂ) (r : ℝ) :
    complexCenteredCubicPhase a t (a+(r:ℂ)*y) =
      r^2*complexCriticalPhase ((a,r),t) y := by
  have he : t*((a+(r:ℂ)*y-a)^3+3*a*(a+(r:ℂ)*y-a)^2) =
      ((r^2:ℝ):ℂ)*(t*(3*a*y^2+(r:ℂ)*y^3)) := by push_cast; ring
  rw [complexCenteredCubicPhase,he,Complex.re_ofReal_mul,complexCriticalPhase]
  ring

theorem scalarOscillatoryPhase_scale (lambda r : ℝ) (phi : ℂ → ℝ) (y : ℂ) :
    scalarOscillatoryPhase lambda (fun x => r*phi x) y =
      scalarOscillatoryPhase (lambda*r) phi y := by
  unfold scalarOscillatoryPhase
  congr 1
  push_cast
  ring

def complexLocalizedAmplitude (W : ℂ → ℂ) (r0 : ℝ) (a z : ℂ) : ℂ :=
  W z*(complexDiskCutoff ((z-a)/(r0:ℂ)):ℂ)

theorem complexLocalizedAmplitude_contDiff {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    (r0 : ℝ) (a : ℂ) : ContDiff ℝ ∞ (complexLocalizedAmplitude W r0 a) :=
  hW.mul (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)))

theorem complexLocalizedAmplitude_support {W : ℂ → ℂ} {r0 : ℝ} (hr0 : 0 < r0) (a : ℂ) :
    support (complexLocalizedAmplitude W r0 a) ⊆ closedBall a (2*r0) := by
  intro z hz
  simp only [mem_closedBall,dist_eq_norm]
  by_contra hn
  have hnorm : 2 ≤ ‖(z-a)/(r0:ℂ)‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0]
    exact (le_div_iff₀ hr0).mpr (le_of_lt (lt_of_not_ge hn))
  apply hz
  simp only [complexLocalizedAmplitude,complexDiskCutoff_zero hnorm,Complex.ofReal_zero,mul_zero]

theorem complexLocalizedAmplitude_norm_le {W : ℂ → ℂ} (hW : ∀ z, ‖W z‖ ≤ 1)
    (r0 : ℝ) (a z : ℂ) : ‖complexLocalizedAmplitude W r0 a z‖ ≤ 1 := by
  rw [complexLocalizedAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (complexDiskCutoff_nonneg _)]
  exact mul_le_one₀ (hW z) (complexDiskCutoff_nonneg _) (complexDiskCutoff_le_one _)

def complexShellAmplitude (W : ℂ → ℂ) (r0 : ℝ)
    (q : ComplexCriticalParameter × ℂ) : ℂ :=
  W (q.1.1.1+(q.1.1.2:ℂ)*q.2) *
    (complexDiskCutoff (((q.1.1.2/r0:ℝ):ℂ)*q.2):ℂ) *
    (complexAnnularCutoff q.2:ℂ)

theorem complexShellAmplitude_contDiff {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W) (r0 : ℝ) :
    ContDiff ℝ ∞ (complexShellAmplitude W r0) := by
  have ha : ContDiff ℝ ∞ (fun q : ComplexCriticalParameter × ℂ => q.1.1.1) := by fun_prop
  have hr : ContDiff ℝ ∞ (fun q : ComplexCriticalParameter × ℂ => q.1.1.2) := by fun_prop
  exact ((hW.comp (ha.add ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_snd))).mul
    (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
      ((Complex.ofRealCLM.contDiff.comp (hr.div_const _)).mul contDiff_snd)))).mul
    (Complex.ofRealCLM.contDiff.comp (complexAnnularCutoff_contDiff.comp contDiff_snd))

theorem complexShellAmplitude_support (W : ℂ → ℂ) (r0 : ℝ) (p : ComplexCriticalParameter) :
    support (fun y => complexShellAmplitude W r0 (p,y)) ⊆ complexUnitAnnulus := by
  intro y hy
  apply complexAnnularCutoff_support
  intro hz
  apply hy
  simp only [complexShellAmplitude,hz,Complex.ofReal_zero,mul_zero]

def complexShellIntegral (W : ℂ → ℂ) (r0 : ℝ) (a t : ℂ) (lambda r : ℝ) : ℂ :=
  ∫ z, complexLocalizedAmplitude W r0 a z *
    (complexAnnularCutoff ((z-a)/(r:ℂ)):ℂ) *
    scalarOscillatoryPhase lambda (complexCenteredCubicPhase a t) z

theorem complexShellIntegral_scale (W : ℂ → ℂ) {r0 r : ℝ} (hr : 0 < r)
    (a t : ℂ) (lambda : ℝ) :
    complexShellIntegral W r0 a t lambda r = (r^2:ℝ) •
      ∫ y : ℂ, complexShellAmplitude W r0 (((a,r),t),y) *
        scalarOscillatoryPhase (lambda*r^2) (complexCriticalPhase ((a,r),t)) y := by
  rw [complexShellIntegral,complex_integral_affine _ a hr]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : (a+(r:ℂ)*y-a)/(r:ℂ) = y := by field_simp; ring
  have he0 : (a+(r:ℂ)*y-a)/(r0:ℂ) = ((r/r0:ℝ):ℂ)*y := by push_cast; ring
  simp only [complexLocalizedAmplitude,he,he0,complexShellAmplitude]
  congr 1
  unfold scalarOscillatoryPhase
  rw [complexCenteredCubicPhase_scale]
  congr 1
  push_cast
  ring

theorem complexShellIntegral_zero_of_large (W : ℂ → ℂ) {r0 r : ℝ}
    (hr0 : 0 < r0) (hr : 2*r0 ≤ r) (a t : ℂ) (lambda : ℝ) :
    complexShellIntegral W r0 a t lambda r = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  change _ = (0:ℂ)
  by_cases hloc : complexLocalizedAmplitude W r0 a z = 0
  · simp only [hloc,zero_mul]
  have hs := complexLocalizedAmplitude_support hr0 a hloc
  have hd : ‖z-a‖ ≤ 2*r0 := by simpa only [mem_closedBall,dist_eq_norm] using hs
  have hrp : 0 < r := lt_of_lt_of_le (by positivity : 0 < 2*r0) hr
  have hn : ‖(z-a)/(r:ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrp]
    exact (div_le_one hrp).mpr (hd.trans hr)
  have hn2 : ‖((z-a)/(r:ℂ))/2‖ ≤ 1 := by
    norm_num only [norm_div,Complex.norm_ofNat] at *
    linarith
  simp only [complexAnnularCutoff,complexDiskCutoff_one hn,complexDiskCutoff_one hn2,
    sub_self,Complex.ofReal_zero,mul_zero,zero_mul]

/-- The actual shell bound after rescaling, valid for every positive shell radius. -/
theorem uniform_complex_shell_bound {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℂ, a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda r : ℝ, 0 < lambda → 0 < r →
        lambda^2*r^2*‖complexShellIntegral W (a0/8) a t lambda r‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_critical_annulus_bound (A := A) ha0
    (complexShellAmplitude_contDiff hW (a0/8)) (complexShellAmplitude_support W (a0/8)) 2
  refine ⟨C,hC,fun a t ha hA ht lambda r hl hr => ?_⟩
  by_cases hlarge : 2*(a0/8) ≤ r
  · rw [complexShellIntegral_zero_of_large W (by positivity) hlarge a t lambda,norm_zero,mul_zero]
    exact hC.le
  have hp : ((a,r),t) ∈ complexCriticalParameterSet a0 A := by
    refine ⟨⟨⟨?_,ha⟩,⟨hr.le,by linarith⟩⟩,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hA
    · simpa only [mem_sphere,dist_zero_right] using ht
  have hbound := hb ((a,r),t) hp (lambda*r^2)
  rw [abs_of_pos (mul_pos hl (sq_pos_of_pos hr))] at hbound
  rw [complexShellIntegral_scale W hr,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  convert hbound using 1 <;> ring

#print axioms uniform_complex_shell_bound
end WaringSiegel.WSL3
