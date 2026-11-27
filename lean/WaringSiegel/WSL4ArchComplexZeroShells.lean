import WaringSiegel.WSL4ArchComplexZeroDecomposition

/-!
# Rescaled complex annuli with a single uniform stationary constant

The amplitude family f(r*y) times a fixed annular cutoff is jointly smooth
for r in a compact interval including zero. The proved compact-family theorem
therefore yields the radius-uniform bound needed by the cubic dyadic sum.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

def complexScaledAnnularAmplitude (f : ℂ → ℂ) (q : ℝ × ℂ) : ℂ :=
  f ((q.1:ℂ)*q.2)*(complexAnnularCutoff q.2:ℂ)

theorem complexScaledAnnularAmplitude_contDiff {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (complexScaledAnnularAmplitude f) :=
  (hf.comp ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_snd)).mul
    (Complex.ofRealCLM.contDiff.comp (complexAnnularCutoff_contDiff.comp contDiff_snd))

theorem complexScaledAnnularAmplitude_support (f : ℂ → ℂ) (r : ℝ) :
    support (fun y => complexScaledAnnularAmplitude f (r,y)) ⊆
      complexSourceAnnulus 1 4 := by
  intro y hy
  apply complexAnnularCutoff_support
  intro hz
  apply hy
  simp only [complexScaledAnnularAmplitude,hz,Complex.ofReal_zero,mul_zero]

theorem complexScaledAnnularAmplitude_norm_le {f : ℂ → ℂ}
    (hfnorm : ∀ z, ‖f z‖ ≤ 1) (r : ℝ) (y : ℂ) :
    ‖complexScaledAnnularAmplitude f (r,y)‖ ≤ 1 := by
  rw [complexScaledAnnularAmplitude,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_one₀ (hfnorm _) (abs_nonneg _) (complexAnnularCutoff_abs_le _)

/-- The precise radius-uniform shell estimate, including every linear twist. -/
theorem uniform_complex_zero_shell_bound {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hfnorm : ∀ z, ‖f z‖ ≤ 1) (hR : 0 ≤ R)
    (hfs : support f ⊆ closedBall 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ, ∀ r : ℝ, 0 < r →
      ‖theta‖*r*‖complexNearZeroShellIntegral f theta u r‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complex_cubic_annular_stationary_family
    (complexScaledAnnularAmplitude_contDiff hf)
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) (R+1)))
    (fun r _ y => complexScaledAnnularAmplitude_norm_le hfnorm r y)
    (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 4)
    (complexScaledAnnularAmplitude_support f)
  refine ⟨C,hC,fun theta u r hr => ?_⟩
  by_cases hlarge : R ≤ r
  · rw [complexNearZeroShellIntegral_zero_of_large hfs hr hlarge,norm_zero,mul_zero]
    exact hC.le
  have hp : r ∈ Set.Icc (0:ℝ) (R+1) := ⟨hr.le,by linarith [le_of_not_ge hlarge]⟩
  have h := hb r hp (theta*(r:ℂ)^3) (u*(r:ℂ))
  have hn : ‖theta*(r:ℂ)^3‖ = ‖theta‖*r^3 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  rw [hn] at h
  rw [complexNearZeroShellIntegral_scale f theta u hr,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  change (1+‖theta‖*r^3) *
    ‖complexCubicOscillatoryIntegral
      (fun y => f ((r:ℂ)*y)*(complexAnnularCutoff y:ℂ))
      (theta*(r:ℂ)^3) (u*(r:ℂ))‖ ≤ C at h
  nlinarith [norm_nonneg (complexCubicOscillatoryIntegral
    (fun y => f ((r:ℂ)*y)*(complexAnnularCutoff y:ℂ))
    (theta*(r:ℂ)^3) (u*(r:ℂ)))]

#print axioms uniform_complex_zero_shell_bound
end WaringSiegel.WSL4

