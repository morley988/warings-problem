import WaringSiegel.WSL3UnitComplexShells

/-!
# Uniform complex saddle shells for compact families of amplitudes

The parameter of the amplitude is included in the compact parameter set used
by integration by parts. This supplies one constant for all rescalings.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
set_option maxHeartbeats 1000000

theorem uniform_complex_critical_annulus_family {a0 A : ℝ} (ha0 : 0 < a0)
    {F : (P × ComplexCriticalParameter) × ℂ → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set P} (hT : IsCompact T)
    (hFs : ∀ p, support (fun y => F (p,y)) ⊆ complexUnitAnnulus) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T ×ˢ complexCriticalParameterSet a0 A, ∀ lambda : ℝ,
      |lambda|^n*‖∫ y : ℂ, F (p,y)*
        scalarOscillatoryPhase lambda (complexCriticalPhase p.2) y‖ ≤ C := by
  let H : (P × ComplexCriticalParameter) × ℂ → ℂ :=
    fun q => complexCriticalDerivative q.1.2 q.2
  have hH : ContDiff ℝ ∞ H := complexCriticalDerivative_contDiff.comp
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  apply uniform_complex_gradient_integral_bound hF hH
    (hT.prod (complexCriticalParameterSet_isCompact a0 A))
    complexUnitAnnulus_isCompact hFs
    (fun p _ => complexCriticalPhase_contDiff p.2)
  · intro p hp y
    rw [complexCriticalPhase_fderiv,mul_one]
  · intro p hp y
    rw [complexCriticalPhase_fderiv]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
    ring
  · exact ha0
  · intro p hp y hy
    apply complexCriticalDerivative_gap ha0 hp.2
    exact (closure_minimal (hFs p) complexUnitAnnulus_isCompact.isClosed) hy

def complexShellAmplitudeFamily (F : P × ℂ → ℂ) (r0 : ℝ)
    (q : (P × ComplexCriticalParameter) × ℂ) : ℂ :=
  F (q.1.1,q.1.2.1.1+(q.1.2.1.2:ℂ)*q.2) *
    (complexDiskCutoff (((q.1.2.1.2/r0:ℝ):ℂ)*q.2):ℂ) *
    (complexAnnularCutoff q.2:ℂ)

theorem complexShellAmplitudeFamily_contDiff {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) (r0 : ℝ) :
    ContDiff ℝ ∞ (complexShellAmplitudeFamily F r0) := by
  have ha : ContDiff ℝ ∞ (fun q : (P × ComplexCriticalParameter) × ℂ => q.1.2.1.1) := by fun_prop
  have hr : ContDiff ℝ ∞ (fun q : (P × ComplexCriticalParameter) × ℂ => q.1.2.1.2) := by fun_prop
  have hp : ContDiff ℝ ∞ (fun q : (P × ComplexCriticalParameter) × ℂ => q.1.1) := by fun_prop
  exact ((hF.comp (hp.prodMk (ha.add
    ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_snd)))).mul
    (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
      ((Complex.ofRealCLM.contDiff.comp (hr.div_const _)).mul contDiff_snd)))).mul
    (Complex.ofRealCLM.contDiff.comp (complexAnnularCutoff_contDiff.comp contDiff_snd))

theorem complexShellAmplitudeFamily_support (F : P × ℂ → ℂ) (r0 : ℝ)
    (p : P × ComplexCriticalParameter) :
    support (fun y => complexShellAmplitudeFamily F r0 (p,y)) ⊆ complexUnitAnnulus := by
  exact complexShellAmplitude_support (fun z => F (p.1,z)) r0 p.2

/-- The shell constant is uniform over a compact amplitude family. -/
theorem uniform_complex_shell_bound_family {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ a t : ℂ,
      a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda r : ℝ, 0 < lambda → 0 < r →
        lambda^2*r^2*‖complexShellIntegral (fun z => F (p,z))
          (a0/8) a t lambda r‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_critical_annulus_family (A := A) ha0
    (complexShellAmplitudeFamily_contDiff hF (a0/8)) hT
    (complexShellAmplitudeFamily_support F (a0/8)) 2
  refine ⟨C,hC,fun p hp a t ha hA ht lambda r hl hr => ?_⟩
  by_cases hlarge : 2*(a0/8) ≤ r
  · rw [complexShellIntegral_zero_of_large _ (by positivity) hlarge a t lambda,
      norm_zero,mul_zero]
    exact hC.le
  have hpar : ((a,r),t) ∈ complexCriticalParameterSet a0 A := by
    refine ⟨⟨⟨?_,ha⟩,⟨hr.le,by linarith⟩⟩,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hA
    · simpa only [mem_sphere,dist_zero_right] using ht
  have hbound := hb (p,((a,r),t)) ⟨hp,hpar⟩ (lambda*r^2)
  rw [abs_of_pos (mul_pos hl (sq_pos_of_pos hr))] at hbound
  rw [complexShellIntegral_scale _ hr,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r)]
  change (lambda*r^2)^2 *
    ‖∫ y, complexShellAmplitude (fun z => F (p,z)) (a0/8) (((a,r),t),y) *
      scalarOscillatoryPhase (lambda*r^2) (complexCriticalPhase ((a,r),t)) y‖ ≤ C at hbound
  convert hbound using 1 <;> ring

#print axioms uniform_complex_shell_bound_family
end WaringSiegel.WSL4

