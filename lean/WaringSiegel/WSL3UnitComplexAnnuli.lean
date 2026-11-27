import WaringSiegel.WSL3UnitComplexGradient
import WaringSiegel.WSL3UnitCubicPruning

/-!
# Uniform annular cancellation around complex cubic critical points

After translating to a critical point a and rescaling by r, the nonconstant
phase is 2 Re(t(3a y²+r y³)). On a fixed annulus, with r small compared with
|a|, its complex derivative has a fixed positive lower bound. The resulting
arbitrary-power estimate is uniform in all center, scale, and angle parameters.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

/-- A fixed smooth disk cutoff, one on the unit disk and zero beyond radius two. -/
def complexDiskCutoff (z : ℂ) : ℝ := Real.smoothTransition (2-Complex.normSq z)

theorem complexDiskCutoff_contDiff : ContDiff ℝ ∞ complexDiskCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub complex_normSq_contDiff)

theorem complexDiskCutoff_nonneg (z : ℂ) : 0 ≤ complexDiskCutoff z := Real.smoothTransition.nonneg _
theorem complexDiskCutoff_le_one (z : ℂ) : complexDiskCutoff z ≤ 1 := Real.smoothTransition.le_one _

theorem complexDiskCutoff_one {z : ℂ} (hz : ‖z‖ ≤ 1) : complexDiskCutoff z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg z]

theorem complexDiskCutoff_zero {z : ℂ} (hz : 2 ≤ ‖z‖) : complexDiskCutoff z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [Complex.normSq_eq_norm_sq]
  nlinarith

/-- A smooth dyadic annular shell. -/
def complexAnnularCutoff (z : ℂ) : ℝ := complexDiskCutoff (z/2)-complexDiskCutoff z

theorem complexAnnularCutoff_contDiff : ContDiff ℝ ∞ complexAnnularCutoff :=
  (complexDiskCutoff_contDiff.comp (contDiff_id.div_const 2)).sub complexDiskCutoff_contDiff

def complexUnitAnnulus : Set ℂ := closedBall 0 4 ∩ {z | 1 ≤ ‖z‖}

theorem complexUnitAnnulus_isCompact : IsCompact complexUnitAnnulus :=
  (isCompact_closedBall 0 4).inter_right (isClosed_le continuous_const continuous_norm)

theorem complexAnnularCutoff_support : support complexAnnularCutoff ⊆ complexUnitAnnulus := by
  intro z hz
  have hnorm : ‖z/2‖ = ‖z‖/2 := by norm_num [norm_div]
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    by_contra hn
    have h4 : 4 < ‖z‖ := lt_of_not_ge hn
    apply hz
    rw [complexAnnularCutoff,complexDiskCutoff_zero (by rw [hnorm]; linarith),
      complexDiskCutoff_zero (by linarith),sub_self]
  · by_contra hn
    have h1 : ‖z‖ < 1 := lt_of_not_ge hn
    apply hz
    rw [complexAnnularCutoff,complexDiskCutoff_one (by rw [hnorm]; linarith [norm_nonneg z]),
      complexDiskCutoff_one h1.le,sub_self]

theorem complexAnnularCutoff_abs_le (z : ℂ) : |complexAnnularCutoff z| ≤ 1 := by
  rw [complexAnnularCutoff,abs_le]
  constructor <;> linarith [complexDiskCutoff_nonneg z,complexDiskCutoff_le_one z,
    complexDiskCutoff_nonneg (z/2),complexDiskCutoff_le_one (z/2)]

abbrev ComplexCriticalParameter := (ℂ × ℝ) × ℂ

def complexCriticalParameterSet (a0 A : ℝ) : Set ComplexCriticalParameter :=
  ((closedBall 0 A ∩ {a : ℂ | a0 ≤ ‖a‖}) ×ˢ Set.Icc 0 (a0/4)) ×ˢ sphere 0 1

theorem complexCriticalParameterSet_isCompact (a0 A : ℝ) :
    IsCompact (complexCriticalParameterSet a0 A) :=
  (((isCompact_closedBall 0 A).inter_right (isClosed_le continuous_const continuous_norm)).prod
    isCompact_Icc).prod (isCompact_sphere 0 1)

def complexCriticalPhase (p : ComplexCriticalParameter) (y : ℂ) : ℝ :=
  2*(p.2*(3*p.1.1*y^2+(p.1.2:ℂ)*y^3)).re

def complexCriticalDerivative (p : ComplexCriticalParameter) (y : ℂ) : ℂ :=
  p.2*(6*p.1.1*y+3*(p.1.2:ℂ)*y^2)

theorem complexCriticalPhase_contDiff (p : ComplexCriticalParameter) :
    ContDiff ℝ ∞ (complexCriticalPhase p) :=
  contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul
    ((contDiff_const.mul (contDiff_id.pow 2)).add (contDiff_const.mul (contDiff_id.pow 3)))))

theorem complexCriticalDerivative_contDiff :
    ContDiff ℝ ∞ (fun q : ComplexCriticalParameter × ℂ => complexCriticalDerivative q.1 q.2) := by
  have ha : ContDiff ℝ ∞ (fun q : ComplexCriticalParameter × ℂ => q.1.1.1) :=
    contDiff_fst.comp (contDiff_fst.comp contDiff_fst)
  have hr : ContDiff ℝ ∞ (fun q : ComplexCriticalParameter × ℂ => (q.1.1.2:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_snd.comp (contDiff_fst.comp contDiff_fst))
  have ht : ContDiff ℝ ∞ (fun q : ComplexCriticalParameter × ℂ => q.1.2) :=
    contDiff_snd.comp contDiff_fst
  exact ht.mul (((contDiff_const.mul ha).mul contDiff_snd).add
    ((contDiff_const.mul hr).mul (contDiff_snd.pow 2)))

theorem complexCriticalPhase_fderiv (p : ComplexCriticalParameter) (y v : ℂ) :
    fderiv ℝ (complexCriticalPhase p) y v = 2*(complexCriticalDerivative p y*v).re := by
  have hg := ((((hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℂ) 2 (x := y)).const_mul (3*p.1.1)).add
    ((hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℂ) 3 (x := y)).const_mul (p.1.2:ℂ))).const_mul p.2)
  have h := (Complex.reCLM.hasFDerivAt.comp y hg).const_mul (2:ℝ)
  change HasFDerivAt (complexCriticalPhase p) _ y at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,Complex.reCLM_apply,smul_eq_mul]
  norm_num [complexCriticalDerivative]
  ring

theorem complexCriticalDerivative_gap {a0 A : ℝ} (ha0 : 0 < a0)
    {p : ComplexCriticalParameter} (hp : p ∈ complexCriticalParameterSet a0 A)
    {y : ℂ} (hy : y ∈ complexUnitAnnulus) : a0 ≤ ‖complexCriticalDerivative p y‖ := by
  have ha : a0 ≤ ‖p.1.1‖ := hp.1.1.2
  have hr0 := hp.1.2.1
  have hr := hp.1.2.2
  have ht : ‖p.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.2
  have hy4 : ‖y‖ ≤ 4 := by simpa only [mem_closedBall,dist_zero_right] using hy.1
  have hy1 : 1 ≤ ‖y‖ := hy.2
  have hnr : ‖(p.1.2:ℂ)*y‖ = p.1.2*‖y‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
  have hna : ‖(2:ℂ)*p.1.1‖ = 2*‖p.1.1‖ := by norm_num [norm_mul]
  have htri : ‖(2:ℂ)*p.1.1‖ ≤ ‖2*p.1.1+(p.1.2:ℂ)*y‖+‖(p.1.2:ℂ)*y‖ := by
    have h := norm_sub_le (2*p.1.1+(p.1.2:ℂ)*y) ((p.1.2:ℂ)*y)
    simpa only [add_sub_cancel_right] using h
  rw [hnr,hna] at htri
  have hm : p.1.2*‖y‖ ≤ a0 := by
    have hprod := mul_le_mul_of_nonneg_left hy4 hr0
    nlinarith
  have hlow : a0 ≤ ‖2*p.1.1+(p.1.2:ℂ)*y‖ := by linarith
  have he : complexCriticalDerivative p y = p.2*(3*y*(2*p.1.1+(p.1.2:ℂ)*y)) := by
    unfold complexCriticalDerivative
    ring
  rw [he,norm_mul,ht,one_mul,norm_mul,norm_mul]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_left hlow (norm_nonneg y)]

/-- The complete compact-parameter annular oscillatory bound. -/
theorem uniform_complex_critical_annulus_bound {a0 A : ℝ} (ha0 : 0 < a0)
    {F : ComplexCriticalParameter × ℂ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hFs : ∀ p, support (fun y => F (p,y)) ⊆ complexUnitAnnulus) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ complexCriticalParameterSet a0 A, ∀ lambda : ℝ,
      |lambda|^n*‖∫ y : ℂ, F (p,y)*scalarOscillatoryPhase lambda (complexCriticalPhase p) y‖ ≤ C := by
  apply uniform_complex_gradient_integral_bound hF complexCriticalDerivative_contDiff
    (complexCriticalParameterSet_isCompact a0 A) complexUnitAnnulus_isCompact hFs
    (fun p _ => complexCriticalPhase_contDiff p)
  · intro p hp y
    rw [complexCriticalPhase_fderiv,mul_one]
  · intro p hp y
    rw [complexCriticalPhase_fderiv]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
    ring
  · exact ha0
  · intro p hp y hy
    apply complexCriticalDerivative_gap ha0 hp
    exact (closure_minimal (hFs p) complexUnitAnnulus_isCompact.isClosed) hy

#print axioms uniform_complex_critical_annulus_bound
end WaringSiegel.WSL3
