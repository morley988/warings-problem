import WaringSiegel.WSL3PoissonTraceSchwartz
import WaringSiegel.WSL3UnitParametricNonstationary

/-!
# Uniform Fourier decay for compact smooth amplitude families

The parameter family may contain translated products of a fixed weight.
Repeated directional integration by parts is applied on the compact unit
sphere. Every Fourier bound is uniform in the amplitude parameter.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module Function
open scoped ContDiff FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
open WaringSiegel.WSL3
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem fourierIntegral_eq_normalized_phase (f : E → ℂ) (ξ : E) (hξ : ξ ≠ 0) :
    (∫ x, f x * scalarOscillatoryPhase (-2*Real.pi*‖ξ‖)
      (fun x => inner ℝ ((‖ξ‖⁻¹:ℝ) • ξ) x) x) = 𝓕 f ξ := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with x
  unfold scalarOscillatoryPhase
  rw [smul_eq_mul, mul_comm (f x)]
  congr 1
  congr 1
  dsimp only
  rw [real_inner_smul_left, real_inner_comm ξ x]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  have hnc : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  push_cast
  field_simp [hnc]

theorem uniform_fourier_polynomial_bound [Nontrivial E]
    {F : P × E → ℂ} (hF : ContDiff ℝ ∞ F)
    {T : Set P} {S : Set E} (hT : IsCompact T) (hS : IsCompact S)
    (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ ξ : E,
      (1+‖ξ‖)^n * ‖𝓕 (fun x => F (p,x)) ξ‖ ≤ C := by
  let A : (P × E) × E → ℂ := fun _ => 1
  let v : P × E → E := Prod.snd
  let G : (P × E) × E → ℂ := fun q => F (q.1.1,q.2)
  let phi : P × E → E → ℝ := fun q x => inner ℝ q.2 x
  have hA : ContDiff ℝ ∞ A := contDiff_const
  have hv : ContDiff ℝ ∞ v := contDiff_snd
  have hG : ContDiff ℝ ∞ G := hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hcompact : IsCompact (T ×ˢ Metric.sphere (0:E) 1) := hT.prod (isCompact_sphere _ _)
  have hGs : ∀ q : P × E, support (fun x => G (q,x)) ⊆ S := fun q => hFs q.1
  have hphi (q : P × E) (_hq : q ∈ T ×ˢ Metric.sphere (0:E) 1) :
      ContDiff ℝ ∞ (phi q) := (InnerProductSpace.toDual ℝ E q.2).contDiff
  have hrecip (q : P × E) (hq : q ∈ T ×ˢ Metric.sphere (0:E) 1) (x : E) (_hx : x ∈ S) :
      A (q,x) * (fderiv ℝ (phi q) x (v q):ℂ) = 1 := by
    have hn : ‖q.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hq.2
    change (1:ℂ) * (fderiv ℝ (InnerProductSpace.toDual ℝ E q.2) x q.2:ℂ) = 1
    rw [ContinuousLinearMap.fderiv]
    change (1:ℂ) * (inner ℝ q.2 q.2:ℂ) = 1
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  obtain ⟨C0, hC0, hb0⟩ := uniform_parameter_nonstationary_integral_bound
    hA hv hG hcompact hS hGs hphi hrecip 0
  obtain ⟨Cn, hCn, hbn⟩ := uniform_parameter_nonstationary_integral_bound
    hA hv hG hcompact hS hGs hphi hrecip n
  refine ⟨(2:ℝ)^n*(C0+Cn), by positivity, fun p hp ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst ξ
    obtain ⟨z, hz⟩ := exists_ne (0:E)
    let b : E := (‖z‖⁻¹:ℝ) • z
    have hb : ‖b‖ = 1 := norm_smul_inv_norm hz
    have hq : (p,b) ∈ T ×ˢ Metric.sphere (0:E) 1 :=
      ⟨hp, by simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩
    have ht := hb0 (p,b) hq 0
    simp only [pow_zero, one_mul, G, scalarOscillatoryPhase, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one] at ht
    have hf : 𝓕 (fun x => F (p,x)) 0 = ∫ x, F (p,x) := by
      rw [Real.fourierIntegral_eq']
      simp
    simp only [norm_zero, add_zero, one_pow, one_mul, hf]
    apply ht.trans
    have hp2 : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    nlinarith
  · let b : E := (‖ξ‖⁻¹:ℝ) • ξ
    let lambda : ℝ := -2*Real.pi*‖ξ‖
    have hb : ‖b‖ = 1 := norm_smul_inv_norm hξ
    have hq : (p,b) ∈ T ×ˢ Metric.sphere (0:E) 1 :=
      ⟨hp, by simpa only [Metric.mem_sphere, dist_zero_right] using hb⟩
    have he : (∫ x, G ((p,b),x) * scalarOscillatoryPhase lambda (phi (p,b)) x) =
        𝓕 (fun x => F (p,x)) ξ := fourierIntegral_eq_normalized_phase _ ξ hξ
    have h0 := hb0 (p,b) hq lambda
    have hn := hbn (p,b) hq lambda
    rw [he] at h0 hn
    simp only [pow_zero, one_mul] at h0
    have hl : ‖ξ‖ ≤ |lambda| := by
      dsimp [lambda]
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_pos Real.pi_pos]
      norm_num
      nlinarith [norm_nonneg ξ, Real.two_le_pi]
    by_cases hsmall : ‖ξ‖ ≤ 1
    · have hp2 : (1+‖ξ‖)^n ≤ (2:ℝ)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      calc
        _ ≤ (2:ℝ)^n * C0 := mul_le_mul hp2 h0 (norm_nonneg _) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have hlarge : 1 ≤ ‖ξ‖ := (lt_of_not_ge hsmall).le
      have hp2 : (1+‖ξ‖)^n ≤ (2:ℝ)^n * |lambda|^n := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) n
      calc
        _ ≤ ((2:ℝ)^n * |lambda|^n) * ‖𝓕 (fun x => F (p,x)) ξ‖ :=
          mul_le_mul_of_nonneg_right hp2 (norm_nonneg _)
        _ = (2:ℝ)^n * (|lambda|^n * ‖𝓕 (fun x => F (p,x)) ξ‖) := by ring
        _ ≤ (2:ℝ)^n * Cn := mul_le_mul_of_nonneg_left hn (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end WaringSiegel.WSL3Poisson
