import WaringSiegel.WSL4ArchComplexAnnular

/-! # Exact complex dyadic decomposition about the degenerate cubic point -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

def complexCubicPhase (theta u z : ℂ) : ℂ :=
  Complex.exp (Complex.I*(2*(theta*z^3+u*z).re : ℝ))

theorem complexCubicPhase_contDiff (theta u : ℂ) :
    ContDiff ℝ ∞ (complexCubicPhase theta u) := by
  have hphi : ContDiff ℝ ∞ (fun z : ℂ => 2*(theta*z^3+u*z).re) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_id.pow 3)).add (contDiff_const.mul contDiff_id)))
  have h := scalarOscillatoryPhase_contDiff (1:ℝ) hphi
  have he : complexCubicPhase theta u =
      scalarOscillatoryPhase 1 (fun z : ℂ => 2*(theta*z^3+u*z).re) := by
    funext z
    simp only [scalarOscillatoryPhase,Complex.ofReal_one,one_mul,complexCubicPhase]
  rw [he]
  exact h

theorem complexCubicPhase_norm (theta u z : ℂ) : ‖complexCubicPhase theta u z‖ = 1 := by
  simpa only [scalarOscillatoryPhase,Complex.ofReal_one,one_mul,complexCubicPhase] using
    scalarOscillatoryPhase_norm (1:ℝ) (fun y : ℂ => 2*(theta*y^3+u*y).re) z

theorem complex_compact_integrable_mul {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hfs : support f ⊆ closedBall 0 R)
    {g : ℂ → ℂ} (hg : Continuous g) : Integrable (fun z => f z*g z) :=
  (hf.mul hg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) hfs).mul_right

def complexNearZeroInnerIntegral (f : ℂ → ℂ) (theta u : ℂ) (delta : ℝ) : ℂ :=
  ∫ z, f z*(complexDiskCutoff (z/(delta:ℂ)):ℂ)*complexCubicPhase theta u z

def complexNearZeroShellIntegral (f : ℂ → ℂ) (theta u : ℂ) (r : ℝ) : ℂ :=
  ∫ z, f z*(complexAnnularCutoff (z/(r:ℂ)):ℂ)*complexCubicPhase theta u z

theorem complexNearZeroInnerIntegral_bound {f : ℂ → ℂ}
    (hfnorm : ∀ z, ‖f z‖ ≤ 1) (theta u : ℂ) {delta : ℝ} (hd : 0 < delta) :
    ‖complexNearZeroInnerIntegral f theta u delta‖ ≤
      delta^2*volume.real (closedBall (0:ℂ) 2) := by
  rw [complexNearZeroInnerIntegral,complex_integral_affine _ 0 hd,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg delta)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg delta)
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 2)
  · intro y hy
    have he : (0+(delta:ℂ)*y)/(delta:ℂ) = y := by
      have hn : (delta:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    simp only [mem_closedBall,dist_zero_right]
    by_contra hn
    apply hy
    dsimp only
    rw [he,complexDiskCutoff_zero (le_of_lt (lt_of_not_ge hn)),
      Complex.ofReal_zero,mul_zero,zero_mul]
  · intro y
    rw [norm_mul,norm_mul,complexCubicPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (complexDiskCutoff_nonneg _)]
    exact mul_le_one₀ (hfnorm _) (complexDiskCutoff_nonneg _) (complexDiskCutoff_le_one _)

/-- The whole compact source, including the origin, has this exact finite decomposition. -/
theorem complexCubicOscillatoryIntegral_dyadic {f : ℂ → ℂ} {R delta : ℝ}
    (hf : Continuous f) (hfs : support f ⊆ closedBall 0 R) (hd : 0 < delta)
    (theta u : ℂ) {N : ℕ} (hN : R ≤ (2:ℝ)^N*delta) :
    complexCubicOscillatoryIntegral f theta u =
      complexNearZeroInnerIntegral f theta u delta +
        ∑ j ∈ Finset.range N, complexNearZeroShellIntegral f theta u ((2:ℝ)^j*delta) := by
  let phase := complexCubicPhase theta u
  have hp : Continuous phase := (complexCubicPhase_contDiff theta u).continuous
  have hinner : Integrable (fun z => f z *
      (complexDiskCutoff (z/(delta:ℂ)):ℂ)*phase z) := by
    simp only [mul_assoc]
    exact complex_compact_integrable_mul hf hfs
      ((Complex.continuous_ofReal.comp (complexDiskCutoff_contDiff.continuous.comp
        (continuous_id.div_const _))).mul hp)
  have hshell : ∀ j, Integrable (fun z => f z *
      (complexAnnularCutoff (z/(((2:ℝ)^j*delta:ℝ):ℂ)):ℂ)*phase z) := by
    intro j
    simp only [mul_assoc]
    exact complex_compact_integrable_mul hf hfs
      ((Complex.continuous_ofReal.comp (complexAnnularCutoff_contDiff.continuous.comp
        (continuous_id.div_const _))).mul hp)
  change (∫ z, f z*phase z) =
    (∫ z, f z*(complexDiskCutoff (z/(delta:ℂ)):ℂ)*phase z) +
      ∑ j ∈ Finset.range N, ∫ z, f z*
        (complexAnnularCutoff (z/(((2:ℝ)^j*delta:ℝ):ℂ)):ℂ)*phase z
  rw [← integral_finset_sum _ (fun j _ => hshell j),← integral_add hinner
    (integrable_finset_sum _ (fun j _ => hshell j))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hfz : f z = 0
  · simp only [hfz,zero_mul,Finset.sum_const_zero,add_zero]
  have hs := hfs hfz
  have hz : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hs
  have hpN : 0 < (2:ℝ)^N*delta := by positivity
  have hnorm : ‖z/(((2:ℝ)^N*delta:ℝ):ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpN]
    exact (div_le_one hpN).mpr (hz.trans hN)
  have hid := complex_dyadic_cutoff_identity z delta N
  rw [complexDiskCutoff_one hnorm] at hid
  have hidC : (complexDiskCutoff (z/(delta:ℂ)):ℂ) +
      ∑ j ∈ Finset.range N, (complexAnnularCutoff (z/(((2:ℝ)^j*delta:ℝ):ℂ)):ℂ) = 1 := by
    exact_mod_cast hid
  rw [← Finset.sum_mul,← Finset.mul_sum,← add_mul,← mul_add,hidC,mul_one]

/-- The exact two-dimensional Jacobian and cubic/linear frequency scaling. -/
theorem complexNearZeroShellIntegral_scale (f : ℂ → ℂ) (theta u : ℂ)
    {r : ℝ} (hr : 0 < r) :
    complexNearZeroShellIntegral f theta u r = (r^2:ℝ) •
      complexCubicOscillatoryIntegral
        (fun y => f ((r:ℂ)*y)*(complexAnnularCutoff y:ℂ))
        (theta*(r:ℂ)^3) (u*(r:ℂ)) := by
  rw [complexNearZeroShellIntegral,complex_integral_affine _ 0 hr]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : ((r:ℂ)*y)/(r:ℂ) = y := by field_simp
  simp only [zero_add,he]
  have hphase : theta*((r:ℂ)*y)^3+u*((r:ℂ)*y) =
      (theta*(r:ℂ)^3)*y^3+(u*(r:ℂ))*y := by ring
  unfold complexCubicPhase
  rw [hphase]

theorem complexNearZeroShellIntegral_zero_of_large {f : ℂ → ℂ} {R r : ℝ}
    (hfs : support f ⊆ closedBall 0 R) (hr : 0 < r) (hRr : R ≤ r)
    (theta u : ℂ) : complexNearZeroShellIntegral f theta u r = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  change _ = (0:ℂ)
  by_cases hfz : f z = 0
  · simp only [hfz,zero_mul]
  have hs := hfs hfz
  have hz : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hs
  have hn : ‖z/(r:ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_one hr).mpr (hz.trans hRr)
  have hn2 : ‖(z/(r:ℂ))/2‖ ≤ 1 := by
    norm_num only [norm_div,Complex.norm_ofNat] at *
    linarith
  simp only [complexAnnularCutoff,complexDiskCutoff_one hn,complexDiskCutoff_one hn2,
    sub_self,Complex.ofReal_zero,mul_zero,zero_mul]

#print axioms complexCubicOscillatoryIntegral_dyadic
#print axioms complexNearZeroShellIntegral_scale
end WaringSiegel.WSL4

