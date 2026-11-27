import WaringSiegel.WSL3UnitComplexShells

/-!
# Finite dyadic decomposition of a localized complex saddle
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

theorem complex_dyadic_cutoff_identity (z : ℂ) (delta : ℝ) (N : ℕ) :
    complexDiskCutoff (z/(delta:ℂ)) +
      ∑ j ∈ Finset.range N, complexAnnularCutoff (z/(((2:ℝ)^j*delta:ℝ):ℂ)) =
        complexDiskCutoff (z/(((2:ℝ)^N*delta:ℝ):ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,← add_assoc,ih,complexAnnularCutoff]
    have he : (z/(((2:ℝ)^N*delta:ℝ):ℂ))/2 =
        z/(((2:ℝ)^(N+1)*delta:ℝ):ℂ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [he]
    ring

theorem complexLocalizedAmplitude_integrable_mul {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    {r0 : ℝ} (hr0 : 0 < r0) (a : ℂ) {g : ℂ → ℂ} (hg : Continuous g) :
    Integrable (fun z => complexLocalizedAmplitude W r0 a z*g z) := by
  exact ((complexLocalizedAmplitude_contDiff hW r0 a).continuous.mul hg).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a (2*r0))
      (complexLocalizedAmplitude_support hr0 a)).mul_right

def complexLocalizedIntegral (W : ℂ → ℂ) (r0 : ℝ) (a t : ℂ) (lambda : ℝ) : ℂ :=
  ∫ z, complexLocalizedAmplitude W r0 a z *
    scalarOscillatoryPhase lambda (complexCenteredCubicPhase a t) z

def complexInnerIntegral (W : ℂ → ℂ) (r0 : ℝ) (a t : ℂ) (lambda delta : ℝ) : ℂ :=
  ∫ z, complexLocalizedAmplitude W r0 a z *
    (complexDiskCutoff ((z-a)/(delta:ℂ)):ℂ) *
    scalarOscillatoryPhase lambda (complexCenteredCubicPhase a t) z

theorem complexInnerIntegral_bound {W : ℂ → ℂ} (hW : ∀ z, ‖W z‖ ≤ 1)
    (r0 : ℝ) (a t : ℂ) (lambda : ℝ) {delta : ℝ} (hd : 0 < delta) :
    ‖complexInnerIntegral W r0 a t lambda delta‖ ≤
      delta^2*volume.real (closedBall (0:ℂ) 2) := by
  rw [complexInnerIntegral,complex_integral_affine _ a hd,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg delta)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg delta)
  apply compact_integral_norm_le_volume (isCompact_closedBall 0 2)
  · intro y hy
    have he : (a+(delta:ℂ)*y-a)/(delta:ℂ) = y := by
      have hn : (delta:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
      ring
    simp only [mem_closedBall,dist_zero_right]
    by_contra hn
    apply hy
    dsimp only
    rw [he,complexDiskCutoff_zero (le_of_lt (lt_of_not_ge hn)),Complex.ofReal_zero,mul_zero,zero_mul]
  · intro y
    rw [norm_mul,norm_mul,scalarOscillatoryPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (complexDiskCutoff_nonneg _)]
    exact mul_le_one₀ (complexLocalizedAmplitude_norm_le hW _ _ _)
      (complexDiskCutoff_nonneg _) (complexDiskCutoff_le_one _)

theorem complexLocalizedIntegral_dyadic {W : ℂ → ℂ} (hW : ContDiff ℝ ∞ W)
    {r0 delta : ℝ} (hr0 : 0 < r0) (hd : 0 < delta)
    (a t : ℂ) (lambda : ℝ) {N : ℕ} (hN : 2*r0 ≤ (2:ℝ)^N*delta) :
    complexLocalizedIntegral W r0 a t lambda =
      complexInnerIntegral W r0 a t lambda delta +
        ∑ j ∈ Finset.range N, complexShellIntegral W r0 a t lambda ((2:ℝ)^j*delta) := by
  let phase := scalarOscillatoryPhase lambda (complexCenteredCubicPhase a t)
  have hp : Continuous phase :=
    (scalarOscillatoryPhase_contDiff lambda (complexCenteredCubicPhase_contDiff a t)).continuous
  have hinner : Integrable (fun z => complexLocalizedAmplitude W r0 a z *
      (complexDiskCutoff ((z-a)/(delta:ℂ)):ℂ)*phase z) := by
    simp only [mul_assoc]
    exact complexLocalizedAmplitude_integrable_mul hW hr0 a
      ((Complex.continuous_ofReal.comp (complexDiskCutoff_contDiff.continuous.comp
        ((continuous_id.sub continuous_const).div_const _))).mul hp)
  have hshell : ∀ j, Integrable (fun z => complexLocalizedAmplitude W r0 a z *
      (complexAnnularCutoff ((z-a)/(((2:ℝ)^j*delta:ℝ):ℂ)):ℂ)*phase z) := by
    intro j
    simp only [mul_assoc]
    exact complexLocalizedAmplitude_integrable_mul hW hr0 a
      ((Complex.continuous_ofReal.comp (complexAnnularCutoff_contDiff.continuous.comp
        ((continuous_id.sub continuous_const).div_const _))).mul hp)
  change (∫ z, complexLocalizedAmplitude W r0 a z*phase z) =
    (∫ z, complexLocalizedAmplitude W r0 a z*
      (complexDiskCutoff ((z-a)/(delta:ℂ)):ℂ)*phase z) +
      ∑ j ∈ Finset.range N, ∫ z, complexLocalizedAmplitude W r0 a z*
        (complexAnnularCutoff ((z-a)/(((2:ℝ)^j*delta:ℝ):ℂ)):ℂ)*phase z
  rw [← integral_finset_sum _ (fun j _ => hshell j),← integral_add hinner
    (integrable_finset_sum _ (fun j _ => hshell j))]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hloc : complexLocalizedAmplitude W r0 a z = 0
  · simp only [hloc,zero_mul,Finset.sum_const_zero,add_zero]
  have hs := complexLocalizedAmplitude_support hr0 a hloc
  have hz : ‖z-a‖ ≤ 2*r0 := by simpa only [mem_closedBall,dist_eq_norm] using hs
  have hpN : 0 < (2:ℝ)^N*delta := by positivity
  have hnorm : ‖(z-a)/(((2:ℝ)^N*delta:ℝ):ℂ)‖ ≤ 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpN]
    exact (div_le_one hpN).mpr (hz.trans hN)
  have hid := complex_dyadic_cutoff_identity (z-a) delta N
  rw [complexDiskCutoff_one hnorm] at hid
  have hidC : (complexDiskCutoff ((z-a)/(delta:ℂ)):ℂ) +
      ∑ j ∈ Finset.range N, (complexAnnularCutoff ((z-a)/(((2:ℝ)^j*delta:ℝ):ℂ)):ℂ) = 1 := by
    exact_mod_cast hid
  rw [← Finset.sum_mul,← Finset.mul_sum,← add_mul,← mul_add,hidC,mul_one]

/-- Summing the actual annular cancellation gives a uniform inverse-frequency
bound near a nonzero complex cubic critical point. -/
theorem uniform_complex_localized_stationary_bound {W : ℂ → ℂ}
    (hW : ContDiff ℝ ∞ W) (hWnorm : ∀ z, ‖W z‖ ≤ 1)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℂ, a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖complexLocalizedIntegral W (a0/8) a t lambda‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_shell_bound (A := A) hW ha0
  refine ⟨volume.real (closedBall (0:ℂ) 2)+2*C+1,by positivity,?_⟩
  intro a t ha hA ht lambda hl
  let delta := (Real.sqrt lambda)⁻¹
  have hs : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hl
  have hd : 0 < delta := inv_pos.mpr hs
  have hdid : lambda*delta^2 = 1 := by
    dsimp only [delta]
    rw [inv_pow,Real.sq_sqrt hl.le,mul_inv_cancel₀ hl.ne']
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(a0/8)/delta)
  have hpow : (N:ℝ) ≤ (2:ℝ)^N := by
    exact_mod_cast (show N < 2^N from Nat.lt_two_pow_self).le
  have hN' : 2*(a0/8) ≤ (2:ℝ)^N*delta := by
    have hdN := (div_lt_iff₀ hd).mp hN
    exact hdN.le.trans (mul_le_mul_of_nonneg_right hpow hd.le)
  have hdecomp := complexLocalizedIntegral_dyadic hW (by positivity : 0 < a0/8) hd a t lambda hN'
  have hi := complexInnerIntegral_bound hWnorm (a0/8) a t lambda hd
  have hi' : lambda*‖complexInnerIntegral W (a0/8) a t lambda delta‖ ≤
      volume.real (closedBall (0:ℂ) 2) := by
    have h := mul_le_mul_of_nonneg_left hi hl.le
    simpa only [← mul_assoc,hdid,one_mul] using h
  have hshell : ∀ j : ℕ,
      lambda*‖complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta)‖ ≤ C*(1/2:ℝ)^j := by
    intro j
    have h := hb a t ha hA ht lambda ((2:ℝ)^j*delta) hl (by positivity)
    have hp : 0 < (2:ℝ)^j := by positivity
    have he : lambda^2*((2:ℝ)^j*delta)^2 = (2:ℝ)^(2*j)*lambda := by
      calc
        _ = (2:ℝ)^(2*j)*lambda*(lambda*delta^2) := by
          rw [Nat.mul_comm 2 j,pow_mul]
          ring
        _ = _ := by rw [hdid,mul_one]
    rw [he,mul_assoc] at h
    have hhalf : (2:ℝ)^(2*j)*(1/2:ℝ)^j = (2:ℝ)^j := by
      rw [show 2*j=j+j by omega,pow_add,mul_assoc,← mul_pow]
      norm_num
    have hge : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    apply (mul_le_mul_left (by positivity : 0 < (2:ℝ)^(2*j))).mp
    calc
      _ ≤ C := h
      _ ≤ C*(2:ℝ)^j := le_mul_of_one_le_right hC.le hge
      _ = _ := by rw [← mul_assoc,mul_comm ((2:ℝ)^(2*j)) C,mul_assoc,hhalf]
  have hn := norm_add_le (complexInnerIntegral W (a0/8) a t lambda delta)
    (∑ j ∈ Finset.range N, complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta))
  rw [hdecomp]
  have hsum := norm_sum_le (s := Finset.range N)
    (f := fun j => complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta))
  have hsum' : lambda*(∑ j ∈ Finset.range N,
      ‖complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta)‖) ≤ 2*C := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range N, C*(1/2:ℝ)^j := Finset.sum_le_sum (fun j _ => hshell j)
      _ = C*(∑ j ∈ Finset.range N, (1/2:ℝ)^j) := (Finset.mul_sum _ _ _).symm
      _ ≤ C*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hC.le
      _ = _ := by ring
  nlinarith

#print axioms uniform_complex_localized_stationary_bound
end WaringSiegel.WSL3
