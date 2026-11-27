import WaringSiegel.WSL4ArchComplexLocalized
import WaringSiegel.WSL3UnitComplexSaddle

/-! # Separated complex saddles uniformly over a compact amplitude family -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
set_option maxHeartbeats 1000000

def complexSaddleRemainderFamily (F : P × ℂ → ℂ) (r0 : ℝ)
    (q : (P × (ℂ × ℂ)) × ℂ) : ℂ :=
  complexSaddleRemainder (fun z => F (q.1.1,z)) r0 (q.1.2,q.2)

theorem complexSaddleRemainderFamily_contDiff {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) (r0 : ℝ) :
    ContDiff ℝ ∞ (complexSaddleRemainderFamily F r0) := by
  have ha : ContDiff ℝ ∞ (fun q : (P × (ℂ × ℂ)) × ℂ => q.1.2.1) := by fun_prop
  have hp : ContDiff ℝ ∞ (fun q : (P × (ℂ × ℂ)) × ℂ => q.1.1) := by fun_prop
  exact (hF.comp (hp.prodMk contDiff_snd)).mul
    ((contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
      ((contDiff_snd.sub ha).div_const _)))).sub
      (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
        ((contDiff_snd.add ha).div_const _))))

theorem uniform_complex_saddle_remainder_family {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T)
    {S : Set ℂ} (hS : IsCompact S) (hFs : ∀ p, support (fun z => F (p,z)) ⊆ S)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ a t : ℂ,
      a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖∫ z, complexSaddleRemainder (fun y => F (p,y)) (a0/8) ((a,t),z)*
          scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ ≤ C := by
  let H : (P × (ℂ × ℂ)) × ℂ → ℂ :=
    fun q => 3*q.1.2.2*q.2^2+(-3*q.1.2.2*q.1.2.1^2)
  have hH : ContDiff ℝ ∞ H := by fun_prop
  have hgap : ∀ p ∈ T ×ˢ complexSaddleParameterSet a0 A, ∀ z ∈
      tsupport (fun y => complexSaddleRemainderFamily F (a0/8) (p,y)),
      (a0/8)^2 ≤ ‖H (p,z)‖ := by
    intro p hp z hz
    have hts : ‖p.2.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.2.2
    have hzs := complexSaddleRemainder_support_gap
      (W := fun y => F (p.1,y)) ha0 hp.2.1.2 p.2.2 hz
    have he : H (p,z) = 3*p.2.2*((z-p.2.1)*(z+p.2.1)) := by dsimp only [H]; ring
    rw [he,norm_mul,norm_mul,norm_mul,hts]
    norm_num
    have hprod := mul_le_mul hzs.1 hzs.2 (by positivity : 0 ≤ a0/8) (norm_nonneg _)
    nlinarith
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound
    (complexSaddleRemainderFamily_contDiff hF (a0/8)) hH
    (hT.prod (complexSaddleParameterSet_isCompact a0 A)) hS
    (fun p => complexSaddleRemainder_support (hFs p.1) (a0/8) p.2)
    (phi := fun p => complexSaddlePhase p.2.1 p.2.2)
    (fun p _ => complexSaddlePhase_contDiff p.2.1 p.2.2)
    (fun p _ z => complex_cubic_gradient_real p.2.2 (-3*p.2.2*p.2.1^2) z)
    (fun p _ z => complex_cubic_gradient_imag p.2.2 (-3*p.2.2*p.2.1^2) z)
    (by positivity : 0 < (a0/8)^2) hgap 1
  refine ⟨C,hC,fun p hp a t ha hA ht lambda hl => ?_⟩
  have hpar : (a,t) ∈ complexSaddleParameterSet a0 A := by
    refine ⟨⟨?_,ha⟩,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hA
    · simpa only [mem_sphere,dist_zero_right] using ht
  simpa only [pow_one,abs_of_pos hl] using hb (p,(a,t)) ⟨hp,hpar⟩ lambda


/-- Full separated-saddle estimate with one constant for the compact amplitude family. -/
theorem uniform_complex_saddle_stationary_family {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T)
    (hFnorm : ∀ p ∈ T, ∀ z, ‖F (p,z)‖ ≤ 1)
    {S : Set ℂ} (hS : IsCompact S) (hFs : ∀ p, support (fun z => F (p,z)) ⊆ S)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ a t : ℂ,
      a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖∫ z, F (p,z)*scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_localized_stationary_family (A := A) hF hT hFnorm ha0
  obtain ⟨D,hD,hd⟩ := uniform_complex_saddle_remainder_family (A := A) hF hT hS hFs ha0
  refine ⟨2*C+D,by positivity,fun p hp a t ha hA ht lambda hl => ?_⟩
  let W : ℂ → ℂ := fun z => F (p,z)
  have hW : ContDiff ℝ ∞ W := hF.comp (contDiff_const.prodMk contDiff_id)
  have hWs : support W ⊆ S := hFs p
  let phase := scalarOscillatoryPhase lambda (complexSaddlePhase a t)
  have hpc : Continuous phase := (scalarOscillatoryPhase_contDiff lambda
    (complexSaddlePhase_contDiff a t)).continuous
  have hi1 := complexLocalizedAmplitude_integrable_mul hW (by positivity : 0 < a0/8) a hpc
  have hi2 := complexLocalizedAmplitude_integrable_mul hW (by positivity : 0 < a0/8) (-a) hpc
  have hi3 : Integrable (fun z => complexSaddleRemainder W (a0/8) ((a,t),z)*phase z) := by
    exact (((complexSaddleRemainder_contDiff hW (a0/8)).continuous.comp
      (continuous_const.prodMk continuous_id)).mul hpc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hS
        (complexSaddleRemainder_support hWs (a0/8) (a,t))).mul_right
  have he : (∫ z, W z*phase z) =
      (∫ z, complexLocalizedAmplitude W (a0/8) a z*phase z) +
      (∫ z, complexLocalizedAmplitude W (a0/8) (-a) z*phase z) +
      (∫ z, complexSaddleRemainder W (a0/8) ((a,t),z)*phase z) := by
    have hi12 : Integrable (fun z => complexLocalizedAmplitude W (a0/8) a z*phase z +
        complexLocalizedAmplitude W (a0/8) (-a) z*phase z) := hi1.add hi2
    rw [← integral_add hi1 hi2,← integral_add hi12 hi3]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [complexLocalizedAmplitude,complexSaddleRemainder,sub_neg_eq_add]
    ring
  have hb1 := hb p hp a t ha hA ht lambda hl
  rw [complexLocalizedIntegral_norm_saddle] at hb1
  have hb2 := hb p hp (-a) t (by simpa using ha) (by simpa using hA) ht lambda hl
  rw [complexLocalizedIntegral_norm_saddle] at hb2
  have hphase : complexSaddlePhase (-a) t = complexSaddlePhase a t := by
    funext z
    simp only [complexSaddlePhase,neg_sq]
  rw [hphase] at hb2
  have hb3 := hd p hp a t ha hA ht lambda hl
  change lambda*‖∫ z, W z*phase z‖ ≤ _
  rw [he]
  have hn := norm_add_le
    ((∫ z, complexLocalizedAmplitude W (a0/8) a z*phase z)+
      (∫ z, complexLocalizedAmplitude W (a0/8) (-a) z*phase z))
    (∫ z, complexSaddleRemainder W (a0/8) ((a,t),z)*phase z)
  have hn' := norm_add_le (∫ z, complexLocalizedAmplitude W (a0/8) a z*phase z)
    (∫ z, complexLocalizedAmplitude W (a0/8) (-a) z*phase z)
  dsimp only [phase] at *
  nlinarith

#print axioms uniform_complex_saddle_stationary_family
end WaringSiegel.WSL4
