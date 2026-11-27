import WaringSiegel.WSL3UnitComplexDyadic

/-!
# Uniform stationary cancellation for separated complex cubic critical points

The source is split into neighborhoods of the two actual critical points
and a remainder with a genuine complex derivative gap.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

def complexSaddlePhase (a t z : ℂ) : ℝ := 2*(t*z^3+(-3*t*a^2)*z).re

theorem complexSaddlePhase_contDiff (a t : ℂ) : ContDiff ℝ ∞ (complexSaddlePhase a t) :=
  contDiff_const.mul (Complex.reCLM.contDiff.comp
    ((contDiff_const.mul (contDiff_id.pow 3)).add (contDiff_const.mul contDiff_id)))

theorem complexCenteredCubicPhase_eq_saddle (a t z : ℂ) :
    complexCenteredCubicPhase a t z = complexSaddlePhase a t z + 2*(2*t*a^3).re := by
  have he : t*((z-a)^3+3*a*(z-a)^2) = (t*z^3+(-3*t*a^2)*z)+2*t*a^3 := by ring
  rw [complexCenteredCubicPhase,he,Complex.add_re,complexSaddlePhase]
  ring

theorem complexLocalizedIntegral_norm_saddle (W : ℂ → ℂ) (r0 : ℝ)
    (a t : ℂ) (lambda : ℝ) :
    ‖complexLocalizedIntegral W r0 a t lambda‖ =
      ‖∫ z, complexLocalizedAmplitude W r0 a z*scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ := by
  let c := scalarOscillatoryPhase lambda (fun _ : ℂ => 2*(2*t*a^3).re) 0
  have hc : ‖c‖ = 1 := scalarOscillatoryPhase_norm _ _ _
  have he : ∀ z, scalarOscillatoryPhase lambda (complexCenteredCubicPhase a t) z =
      scalarOscillatoryPhase lambda (complexSaddlePhase a t) z*c := by
    intro z
    dsimp only [c,scalarOscillatoryPhase]
    rw [complexCenteredCubicPhase_eq_saddle,Complex.ofReal_add,mul_add,Complex.exp_add]
  simp only [complexLocalizedIntegral,he,← mul_assoc,integral_mul_const,norm_mul,hc,mul_one]

def complexSaddleRemainder (W : ℂ → ℂ) (r0 : ℝ) (q : (ℂ × ℂ) × ℂ) : ℂ :=
  W q.2*(1-(complexDiskCutoff ((q.2-q.1.1)/(r0:ℂ)):ℂ)-
    (complexDiskCutoff ((q.2+q.1.1)/(r0:ℂ)):ℂ))

theorem complexSaddleRemainder_contDiff {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W) (r0 : ℝ) :
    ContDiff ℝ ∞ (complexSaddleRemainder W r0) := by
  have ha : ContDiff ℝ ∞ (fun q : (ℂ × ℂ) × ℂ => q.1.1) := by fun_prop
  exact (hW.comp contDiff_snd).mul
    ((contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
      ((contDiff_snd.sub ha).div_const _)))).sub
      (Complex.ofRealCLM.contDiff.comp (complexDiskCutoff_contDiff.comp
        ((contDiff_snd.add ha).div_const _))))

theorem complexSaddleRemainder_support {W : ℂ → ℂ} {S : Set ℂ}
    (hWs : support W ⊆ S) (r0 : ℝ) (p : ℂ × ℂ) :
    support (fun z => complexSaddleRemainder W r0 (p,z)) ⊆ S := by
  intro z hz
  apply hWs
  intro he
  apply hz
  simp only [complexSaddleRemainder,he,zero_mul]

theorem complexSaddleRemainder_support_gap {W : ℂ → ℂ} {a0 : ℝ} (ha0 : 0 < a0)
    {a : ℂ} (ha : a0 ≤ ‖a‖) (t : ℂ) :
    tsupport (fun z => complexSaddleRemainder W (a0/8) ((a,t),z)) ⊆
      {z | a0/8 ≤ ‖z-a‖} ∩ {z | a0/8 ≤ ‖z+a‖} := by
  have hr : 0 < a0/8 := by positivity
  apply closure_minimal
  · intro z hz
    have hzero : ∀ b : ℂ, b = a ∨ b = -a → ‖z-b‖ < a0/8 →
        complexSaddleRemainder W (a0/8) ((a,t),z) = 0 := by
      intro b hb hzb
      have hbNorm : ‖b‖ = ‖a‖ := by rcases hb with rfl | rfl <;> simp
      have hsep : 2*(a0/8) ≤ ‖z+b‖ := by
        have htri := norm_sub_le (z+b) (z-b)
        have he : z+b-(z-b) = (2:ℂ)*b := by ring
        rw [he,norm_mul,hbNorm] at htri
        norm_num at htri
        linarith
      have hone : complexDiskCutoff ((z-b)/((a0/8:ℝ):ℂ)) = 1 := by
        apply complexDiskCutoff_one
        rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
        exact (div_le_one hr).mpr hzb.le
      have htwo : complexDiskCutoff ((z+b)/((a0/8:ℝ):ℂ)) = 0 := by
        apply complexDiskCutoff_zero
        rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
        exact (le_div_iff₀ hr).mpr hsep
      rcases hb with rfl | rfl
      · simp only [complexSaddleRemainder,hone,htwo,Complex.ofReal_one,Complex.ofReal_zero,
          sub_self,sub_zero,mul_zero]
      · simp only [sub_neg_eq_add,← sub_eq_add_neg] at hone htwo
        simp only [complexSaddleRemainder,hone,htwo,Complex.ofReal_one,Complex.ofReal_zero,
          sub_zero,sub_self,mul_zero]
    constructor
    · by_contra hn
      exact hz (hzero a (Or.inl rfl) (lt_of_not_ge hn))
    · by_contra hn
      have hn' : ‖z-(-a)‖ < a0/8 := by simpa only [sub_neg_eq_add] using lt_of_not_ge hn
      exact hz (hzero (-a) (Or.inr rfl) hn')
  · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le continuous_const (continuous_id.add continuous_const).norm)

def complexSaddleParameterSet (a0 A : ℝ) : Set (ℂ × ℂ) :=
  (closedBall 0 A ∩ {a | a0 ≤ ‖a‖}) ×ˢ sphere 0 1

theorem complexSaddleParameterSet_isCompact (a0 A : ℝ) : IsCompact (complexSaddleParameterSet a0 A) :=
  ((isCompact_closedBall 0 A).inter_right (isClosed_le continuous_const continuous_norm)).prod
    (isCompact_sphere 0 1)

theorem uniform_complex_saddle_remainder_bound {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    {S : Set ℂ} (hS : IsCompact S) (hWs : support W ⊆ S)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℂ, a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖∫ z, complexSaddleRemainder W (a0/8) ((a,t),z)*
          scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ ≤ C := by
  let H : (ℂ × ℂ) × ℂ → ℂ := fun q => 3*q.1.2*q.2^2+(-3*q.1.2*q.1.1^2)
  have hH : ContDiff ℝ ∞ H := by fun_prop
  have hgap : ∀ p ∈ complexSaddleParameterSet a0 A, ∀ z ∈
      tsupport (fun y => complexSaddleRemainder W (a0/8) (p,y)), (a0/8)^2 ≤ ‖H (p,z)‖ := by
    intro p hp z hz
    have hts : ‖p.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.2
    have hzs := complexSaddleRemainder_support_gap ha0 hp.1.2 p.2 hz
    have he : H (p,z) = 3*p.2*((z-p.1)*(z+p.1)) := by dsimp only [H]; ring
    rw [he,norm_mul,norm_mul,norm_mul,hts]
    norm_num
    have hprod := mul_le_mul hzs.1 hzs.2 (by positivity : 0 ≤ a0/8) (norm_nonneg _)
    nlinarith
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound
    (complexSaddleRemainder_contDiff hW (a0/8)) hH
    (complexSaddleParameterSet_isCompact a0 A) hS (complexSaddleRemainder_support hWs (a0/8))
    (phi := fun p => complexSaddlePhase p.1 p.2)
    (fun p _ => complexSaddlePhase_contDiff p.1 p.2)
    (fun p _ z => complex_cubic_gradient_real p.2 (-3*p.2*p.1^2) z)
    (fun p _ z => complex_cubic_gradient_imag p.2 (-3*p.2*p.1^2) z)
    (by positivity : 0 < (a0/8)^2) hgap 1
  refine ⟨C,hC,fun a t ha hA ht lambda hl => ?_⟩
  have hp : (a,t) ∈ complexSaddleParameterSet a0 A := by
    refine ⟨⟨?_,ha⟩,?_⟩
    · simpa only [mem_closedBall,dist_zero_right] using hA
    · simpa only [mem_sphere,dist_zero_right] using ht
  simpa only [pow_one,abs_of_pos hl] using hb (a,t) hp lambda

/-- The complete uniform stationary bound when the two critical points
stay in a fixed compact annulus away from zero. -/
theorem uniform_complex_saddle_stationary_bound {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    (hWnorm : ∀ z, ‖W z‖ ≤ 1) {S : Set ℂ} (hS : IsCompact S) (hWs : support W ⊆ S)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℂ, a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖∫ z, W z*scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_localized_stationary_bound (A := A) hW hWnorm ha0
  obtain ⟨D,hD,hd⟩ := uniform_complex_saddle_remainder_bound (A := A) hW hS hWs ha0
  refine ⟨2*C+D,by positivity,fun a t ha hA ht lambda hl => ?_⟩
  let phase := scalarOscillatoryPhase lambda (complexSaddlePhase a t)
  have hp : Continuous phase := (scalarOscillatoryPhase_contDiff lambda
    (complexSaddlePhase_contDiff a t)).continuous
  have hi1 := complexLocalizedAmplitude_integrable_mul hW (by positivity : 0 < a0/8) a hp
  have hi2 := complexLocalizedAmplitude_integrable_mul hW (by positivity : 0 < a0/8) (-a) hp
  have hi3 : Integrable (fun z => complexSaddleRemainder W (a0/8) ((a,t),z)*phase z) := by
    exact (((complexSaddleRemainder_contDiff hW (a0/8)).continuous.comp
      (continuous_const.prodMk continuous_id)).mul hp).integrable_of_hasCompactSupport
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
  have hb1 := hb a t ha hA ht lambda hl
  rw [complexLocalizedIntegral_norm_saddle] at hb1
  have hb2 := hb (-a) t (by simpa using ha) (by simpa using hA) ht lambda hl
  rw [complexLocalizedIntegral_norm_saddle] at hb2
  have hphase : complexSaddlePhase (-a) t = complexSaddlePhase a t := by
    funext z
    simp only [complexSaddlePhase,neg_sq]
  rw [hphase] at hb2
  have hb3 := hd a t ha hA ht lambda hl
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

#print axioms uniform_complex_saddle_stationary_bound
end WaringSiegel.WSL3
