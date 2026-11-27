import WaringSiegel.WSL3UnitComplexStationary

/-!
# Arbitrary-power frequency decay for smooth pure kth-power phases

The source is supported away from zero. The actual derivative therefore
has a uniform gap after normalizing the frequency direction. Repeated
integration by parts gives every power, for every positive degree k.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

def realPowerOscillatoryIntegral (k : ℕ) (f : ℝ → ℂ) (theta : ℝ) : ℂ :=
  ∫ x, f x*Complex.exp (Complex.I*(theta*x^k : ℝ))

def complexPowerOscillatoryIntegral (k : ℕ) (f : ℂ → ℂ) (theta : ℂ) : ℂ :=
  ∫ z, f z*Complex.exp (Complex.I*(2*(theta*z^k).re : ℝ))

theorem real_power_fderiv (k : ℕ) (x : ℝ) :
    fderiv ℝ (fun y : ℝ => y^k) x 1 = (k:ℝ)*x^(k-1) := by
  rw [fderiv_deriv]
  simpa using (hasDerivAt_pow k x).deriv

theorem real_power_rapid_bound (k : ℕ) (hk : 0 < k) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {rho R : ℝ} (hrho : 0 < rho)
    (hfs : support f ⊆ Set.Icc rho R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℝ,
      |theta|^n*‖realPowerOscillatoryIntegral k f theta‖ ≤ C := by
  let delta := (k:ℝ)*rho^(k-1)
  have hd : 0 < delta := mul_pos (by exact_mod_cast hk) (pow_pos hrho _)
  let A : ℝ × ℝ → ℂ := fun q => (smoothPositiveReciprocal ((k:ℝ)*q.2^(k-1)/delta)/delta:ℝ)
  have hA : ContDiff ℝ ∞ A := Complex.ofRealCLM.contDiff.comp
    ((smoothPositiveReciprocal_contDiff.comp
      ((contDiff_const.mul (contDiff_snd.pow (k-1))).div_const _)).div_const _)
  have hrec : ∀ p ∈ ({0}:Set ℝ), ∀ x ∈ Set.Icc rho R,
      A (p,x)*(fderiv ℝ (fun y : ℝ => y^k) x 1:ℂ) = 1 := by
    intro p hp x hx
    have hD : delta ≤ (k:ℝ)*x^(k-1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrho.le hx.1 _) (Nat.cast_nonneg k)
    have hhalf : 1/2 ≤ (k:ℝ)*x^(k-1)/delta := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have h := smoothPositiveReciprocal_mul hhalf
    have he : (smoothPositiveReciprocal ((k:ℝ)*x^(k-1)/delta)/delta)*
        ((k:ℝ)*x^(k-1)) = 1 := by
      calc
        _ = smoothPositiveReciprocal ((k:ℝ)*x^(k-1)/delta)*((k:ℝ)*x^(k-1)/delta) := by ring
        _ = 1 := h
    dsimp only [A]
    rw [real_power_fderiv]
    exact_mod_cast he
  obtain ⟨C,hC,hb⟩ := uniform_nonstationary_integral_bound hA
    (v := fun _ : ℝ => (1:ℝ)) contDiff_const hf
    (isCompact_singleton : IsCompact ({0}:Set ℝ)) isCompact_Icc hfs
    (phi := fun _ : ℝ => fun x : ℝ => x^k) (fun _ _ => contDiff_id.pow k) hrec n
  refine ⟨C,hC,fun theta => ?_⟩
  have he : realPowerOscillatoryIntegral k f theta =
      ∫ x, f x*scalarOscillatoryPhase theta (fun y : ℝ => y^k) x := by
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    unfold scalarOscillatoryPhase
    congr 1
    push_cast
    ring
  rw [he]
  exact hb 0 (Set.mem_singleton 0) theta

theorem complex_power_fderiv (k : ℕ) (t z v : ℂ) :
    fderiv ℝ (fun y : ℂ => 2*(t*y^k).re) z v =
      2*(((k:ℂ)*t*z^(k-1))*v).re := by
  have hg := (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℂ) k (x := z)).const_mul t
  have h := (Complex.reCLM.hasFDerivAt.comp z hg).const_mul (2:ℝ)
  change HasFDerivAt (fun y : ℂ => 2*(t*y^k).re) _ z at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,Complex.reCLM_apply,smul_eq_mul]
  congr 2
  push_cast
  ring

theorem complex_power_rapid_bound (k : ℕ) (hk : 0 < k) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) {rho R : ℝ} (hrho : 0 < rho)
    (hfs : support f ⊆ complexSourceAnnulus rho R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℂ,
      ‖theta‖^n*‖complexPowerOscillatoryIntegral k f theta‖ ≤ C := by
  let H : ℂ × ℂ → ℂ := fun q => (k:ℂ)*q.1*q.2^(k-1)
  have hH : ContDiff ℝ ∞ H := by fun_prop
  have hphi (t : ℂ) : ContDiff ℝ ∞ (fun z : ℂ => 2*(t*z^k).re) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp (contDiff_const.mul (contDiff_id.pow k)))
  have hd : 0 < (k:ℝ)*rho^(k-1) := mul_pos (by exact_mod_cast hk) (pow_pos hrho _)
  have hgap : ∀ t ∈ sphere (0:ℂ) 1, ∀ z ∈ tsupport f,
      (k:ℝ)*rho^(k-1) ≤ ‖H (t,z)‖ := by
    intro t ht z hz
    have htt : ‖t‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using ht
    have hzs := (closure_minimal hfs (complexSourceAnnulus_isCompact rho R).isClosed) hz
    dsimp only [H]
    rw [norm_mul,norm_mul,norm_pow,htt,mul_one]
    norm_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrho.le hzs.2 _) (Nat.cast_nonneg k)
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound
    (hf.comp contDiff_snd) hH (isCompact_sphere (0:ℂ) 1)
    (complexSourceAnnulus_isCompact rho R) (fun _ => hfs)
    (phi := fun t z => 2*(t*z^k).re) (fun t _ => hphi t)
    (by intro t ht z; simpa only [mul_one] using complex_power_fderiv k t z 1)
    (by
      intro t ht z
      rw [complex_power_fderiv]
      simp only [Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
      ring)
    hd hgap n
  refine ⟨C,hC,fun theta => ?_⟩
  by_cases htheta : theta = 0
  · subst theta
    have h := hb 1 (by simp) 0
    simpa only [complexPowerOscillatoryIntegral,scalarOscillatoryPhase,norm_zero,Complex.ofReal_zero,
      zero_mul,mul_zero,Complex.exp_zero,mul_one,abs_zero,Complex.zero_re,Function.comp_apply] using h
  have hp : 0 < ‖theta‖ := norm_pos_iff.mpr htheta
  have hn : (‖theta‖:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  let t := theta/(‖theta‖:ℂ)
  have ht : t ∈ sphere (0:ℂ) 1 := by
    simp only [t,mem_sphere,dist_zero_right,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hp,div_self hp.ne']
  have he : complexPowerOscillatoryIntegral k f theta =
      ∫ z, f z*scalarOscillatoryPhase ‖theta‖ (fun y : ℂ => 2*(t*y^k).re) z := by
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold scalarOscillatoryPhase
    congr 1
    have he : theta*z^k = (‖theta‖:ℂ)*(t*z^k) := by dsimp only [t]; field_simp
    rw [he,Complex.re_ofReal_mul]
    push_cast
    ring
  rw [he]
  simpa only [abs_of_pos hp] using hb t ht ‖theta‖

theorem one_add_pow_mul_bound {t v C0 Cn : ℝ} (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hC0 : 0 ≤ C0) (hCn : 0 ≤ Cn) (h0 : v ≤ C0) (n : ℕ) (hn : t^n*v ≤ Cn) :
    (1+t)^n*v ≤ 2^n*(C0+Cn) := by
  by_cases hsmall : t ≤ 1
  · have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+t) (by linarith : 1+t ≤ 2) n
    have hm := mul_le_mul hp h0 hv (by positivity : 0 ≤ (2:ℝ)^n)
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]
  · have hp := one_add_pow_bound (le_of_lt (lt_of_not_ge hsmall)) n
    have hm := mul_le_mul_of_nonneg_right hp hv
    have hn' := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2:ℝ)^n)
    nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]

theorem real_power_one_add_rapid_bound (k : ℕ) (hk : 0 < k) {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {rho R : ℝ} (hrho : 0 < rho)
    (hfs : support f ⊆ Set.Icc rho R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℝ,
      (1+|theta|)^n*‖realPowerOscillatoryIntegral k f theta‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := real_power_rapid_bound k hk hf hrho hfs 0
  obtain ⟨Cn,hCn,hn⟩ := real_power_rapid_bound k hk hf hrho hfs n
  refine ⟨2^n*(C0+Cn),by positivity,fun theta => ?_⟩
  apply one_add_pow_mul_bound (abs_nonneg theta) (norm_nonneg _) hC0.le hCn.le _ n (hn theta)
  simpa only [pow_zero,one_mul] using h0 theta

theorem complex_power_one_add_rapid_bound (k : ℕ) (hk : 0 < k) {f : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) {rho R : ℝ} (hrho : 0 < rho)
    (hfs : support f ⊆ complexSourceAnnulus rho R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℂ,
      (1+‖theta‖)^n*‖complexPowerOscillatoryIntegral k f theta‖ ≤ C := by
  obtain ⟨C0,hC0,h0⟩ := complex_power_rapid_bound k hk hf hrho hfs 0
  obtain ⟨Cn,hCn,hn⟩ := complex_power_rapid_bound k hk hf hrho hfs n
  refine ⟨2^n*(C0+Cn),by positivity,fun theta => ?_⟩
  apply one_add_pow_mul_bound (norm_nonneg theta) (norm_nonneg _) hC0.le hCn.le _ n (hn theta)
  simpa only [pow_zero,one_mul] using h0 theta

#print axioms real_power_one_add_rapid_bound
#print axioms complex_power_one_add_rapid_bound
end WaringSiegel.WSL3
