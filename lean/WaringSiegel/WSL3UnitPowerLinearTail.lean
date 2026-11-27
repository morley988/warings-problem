import WaringSiegel.WSL3UnitPowerDecay

/-!
# Uniform arbitrary-degree nonstationary tails with a linear twist

The coefficient of the linear term dominates the derivative of the power
term throughout the compact source. All normalized frequency directions
form a genuine compact family; repeated integration by parts supplies every
inverse power with no assumed decay estimate.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

def powerTailRadius (k : ℕ) (R : ℝ) : ℝ :=
  (2*((k:ℝ)+1)*(1+|R|)^(k-1))⁻¹

theorem powerTailRadius_pos (k : ℕ) (R : ℝ) : 0 < powerTailRadius k R := by
  unfold powerTailRadius
  positivity

theorem powerTailRadius_bound (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (k:ℝ)*powerTailRadius k R*R^(k-1) ≤ 1/2 := by
  have hp : 0 < (1+|R|)^(k-1) := by positivity
  have hd : 0 < 2*((k:ℝ)+1)*(1+|R|)^(k-1) := by positivity
  have hpow : R^(k-1) ≤ (1+|R|)^(k-1) :=
    pow_le_pow_left₀ hR (by linarith [le_abs_self R]) _
  unfold powerTailRadius
  calc
    _ = ((k:ℝ)*R^(k-1))/(2*((k:ℝ)+1)*(1+|R|)^(k-1)) := by ring
    _ ≤ 1/2 := (div_le_iff₀ hd).mpr (by
      have hm := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg k : (0:ℝ) ≤ k)
      nlinarith)

theorem real_power_linear_derivative_pos (k : ℕ) {R t x : ℝ} (hR : 0 ≤ R)
    (ht : |t| ≤ powerTailRadius k R) (hx : |x| ≤ R) :
    1/2 ≤ 1+(k:ℝ)*t*x^(k-1) := by
  have hpow : |x|^(k-1) ≤ R^(k-1) := pow_le_pow_left₀ (abs_nonneg x) hx _
  have hb : |(k:ℝ)*t*x^(k-1)| ≤ 1/2 := calc
    _ = (k:ℝ)*|t| *|x|^(k-1) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg k),abs_pow]
    _ ≤ (k:ℝ)*powerTailRadius k R*R^(k-1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k)) hpow
        (pow_nonneg (abs_nonneg x) _)
        (mul_nonneg (Nat.cast_nonneg k) (powerTailRadius_pos k R).le)
    _ ≤ 1/2 := powerTailRadius_bound k hR
  linarith [neg_abs_le ((k:ℝ)*t*x^(k-1))]

theorem real_power_linear_fderiv (k : ℕ) (t x : ℝ) :
    fderiv ℝ (fun y : ℝ => y+t*y^k) x 1 = 1+(k:ℝ)*t*x^(k-1) := by
  rw [fderiv_deriv]
  have h := ((hasDerivAt_id x).add ((hasDerivAt_pow k x).const_mul t)).deriv
  convert h using 1 <;> ring

def realPowerLinearOscillatoryIntegral (k : ℕ) (f : ℝ → ℂ) (θ u : ℝ) : ℂ :=
  ∫ x, f x*Complex.exp (Complex.I*(θ*x^k+u*x:ℝ))

theorem real_power_linear_nonstationary_bound (k : ℕ) {f : ℝ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R) (hfs : support f ⊆ closedBall 0 R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ u : ℝ,
      |θ| ≤ powerTailRadius k R*|u| →
      |u|^n*‖realPowerLinearOscillatoryIntegral k f θ u‖ ≤ C := by
  let A : ℝ × ℝ → ℂ := fun p => (smoothPositiveReciprocal (1+(k:ℝ)*p.1*p.2^(k-1)):ℝ)
  have hA : ContDiff ℝ ∞ A :=
    Complex.ofRealCLM.contDiff.comp (smoothPositiveReciprocal_contDiff.comp (by fun_prop))
  have hphi (t : ℝ) : ContDiff ℝ ∞ (fun x : ℝ => x+t*x^k) := by fun_prop
  have hr (t : ℝ) (ht : t ∈ closedBall 0 (powerTailRadius k R))
      (x : ℝ) (hx : x ∈ closedBall 0 R) :
      A (t,x)*(fderiv ℝ (fun y : ℝ => y+t*y^k) x (1:ℝ):ℂ) = 1 := by
    have ht' : |t| ≤ powerTailRadius k R := by simpa only [mem_closedBall,Real.dist_eq,sub_zero] using ht
    have hx' : |x| ≤ R := by simpa only [mem_closedBall,Real.dist_eq,sub_zero] using hx
    rw [real_power_linear_fderiv]
    dsimp only [A]
    exact_mod_cast smoothPositiveReciprocal_mul (real_power_linear_derivative_pos k hR ht' hx')
  obtain ⟨C,hC,hb⟩ := uniform_nonstationary_integral_bound hA
    (v := fun _ : ℝ => (1:ℝ)) contDiff_const hf
    (isCompact_closedBall 0 (powerTailRadius k R)) (isCompact_closedBall 0 R) hfs
    (fun t _ => hphi t) hr n
  refine ⟨C,hC,fun θ u hu => ?_⟩
  have ht : θ/u ∈ closedBall 0 (powerTailRadius k R) := by
    simp only [mem_closedBall,Real.dist_eq,sub_zero,abs_div]
    by_cases hz : u = 0
    · simp [hz,(powerTailRadius_pos k R).le]
    · exact (div_le_iff₀ (abs_pos.mpr hz)).mpr hu
  have hθ : θ/u*u = θ := by
    by_cases hz : u = 0
    · have : θ = 0 := by simpa [hz] using hu
      simp [hz,this]
    · exact div_mul_cancel₀ θ hz
  have hi : realPowerLinearOscillatoryIntegral k f θ u =
      ∫ x, f x*scalarOscillatoryPhase u (fun y : ℝ => y+(θ/u)*y^k) x := by
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    unfold scalarOscillatoryPhase
    congr 1
    have he : θ*x^k+u*x = u*(x+(θ/u)*x^k) := by
      calc
        _ = (θ/u*u)*x^k+u*x := by rw [hθ]
        _ = _ := by ring
    rw [he]
    push_cast
    ring
  rw [hi]
  exact hb _ ht u

theorem complex_power_linear_fderiv (k : ℕ) (t xi z v : ℂ) :
    fderiv ℝ (fun y : ℂ => 2*(t*y^k+xi*y).re) z v =
      2*(((k:ℂ)*t*z^(k-1)+xi)*v).re := by
  have hg := (((hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℂ) k (x := z)).const_mul t).add
    ((hasFDerivAt_id z).const_mul xi))
  have h := (Complex.reCLM.hasFDerivAt.comp z hg).const_mul (2:ℝ)
  change HasFDerivAt (fun y : ℂ => 2*(t*y^k+xi*y).re) _ z at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.id_apply,Complex.reCLM_apply,smul_eq_mul]
  congr 2
  push_cast
  ring

def complexPowerLinearOscillatoryIntegral (k : ℕ) (f : ℂ → ℂ) (θ u : ℂ) : ℂ :=
  ∫ z, f z*Complex.exp (Complex.I*(2*(θ*z^k+u*z).re:ℝ))

theorem complex_power_linear_nonstationary_bound (k : ℕ) {f : ℂ → ℂ} {R : ℝ}
    (hf : ContDiff ℝ ∞ f) (hR : 0 ≤ R) (hfs : support f ⊆ closedBall 0 R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ u : ℂ, 1 ≤ ‖u‖ →
      ‖θ‖ ≤ powerTailRadius k R*‖u‖ →
      ‖u‖^n*‖complexPowerLinearOscillatoryIntegral k f θ u‖ ≤ C := by
  let H : (ℂ × ℂ) × ℂ → ℂ := fun q => (k:ℂ)*q.1.1*q.2^(k-1)+q.1.2
  have hH : ContDiff ℝ ∞ H := by fun_prop
  let T : Set (ℂ × ℂ) := closedBall 0 (powerTailRadius k R) ×ˢ sphere 0 1
  have hT : IsCompact T := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hphi (p : ℂ × ℂ) : ContDiff ℝ ∞ (fun z : ℂ => 2*(p.1*z^k+p.2*z).re) :=
    contDiff_const.mul (Complex.reCLM.contDiff.comp
      ((contDiff_const.mul (contDiff_id.pow k)).add (contDiff_const.mul contDiff_id)))
  have hgap : ∀ p ∈ T, ∀ z ∈ tsupport f, (1/2:ℝ) ≤ ‖H (p,z)‖ := by
    intro p hp z hz
    have ht : ‖p.1‖ ≤ powerTailRadius k R := by simpa only [mem_closedBall,dist_zero_right] using hp.1
    have hxi : ‖p.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.2
    have hz' : ‖z‖ ≤ R := by
      have hh := (closure_minimal hfs isClosed_closedBall) hz
      simpa only [mem_closedBall,dist_zero_right] using hh
    have hsmall : ‖(k:ℂ)*p.1*z^(k-1)‖ ≤ 1/2 := by
      rw [norm_mul,norm_mul,norm_pow,Complex.norm_natCast]
      exact (mul_le_mul (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k))
        (pow_le_pow_left₀ (norm_nonneg z) hz' _) (by positivity)
        (mul_nonneg (Nat.cast_nonneg k) (powerTailRadius_pos k R).le)).trans
        (powerTailRadius_bound k hR)
    have htri := norm_sub_le (H (p,z)) ((k:ℂ)*p.1*z^(k-1))
    have he : H (p,z) - (k:ℂ)*p.1*z^(k-1) = p.2 := by dsimp only [H]; ring
    rw [he,hxi] at htri
    linarith
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound
    (hf.comp contDiff_snd) hH hT (isCompact_closedBall 0 R) (fun _ => hfs)
    (phi := fun p z => 2*(p.1*z^k+p.2*z).re) (fun p _ => hphi p)
    (by intro p hp z; simpa only [mul_one] using complex_power_linear_fderiv k p.1 p.2 z 1)
    (by
      intro p hp z
      rw [complex_power_linear_fderiv]
      simp only [Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
      ring)
    (by norm_num : (0:ℝ) < 1/2) hgap n
  refine ⟨C,hC,fun θ u hu hθ => ?_⟩
  have hu_pos : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  have hu0 : (‖u‖:ℂ) ≠ 0 := by exact_mod_cast hu_pos.ne'
  have hn (z : ℂ) : ‖z/(‖u‖:ℂ)‖ = ‖z‖/‖u‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg u)]
  have hp : (θ/(‖u‖:ℂ),u/(‖u‖:ℂ)) ∈ T := by
    constructor
    · simpa only [mem_closedBall,dist_zero_right,hn] using (div_le_iff₀ hu_pos).mpr hθ
    · simp only [mem_sphere,dist_zero_right,hn,div_self hu_pos.ne']
  have hi : complexPowerLinearOscillatoryIntegral k f θ u =
      ∫ z, f z*scalarOscillatoryPhase ‖u‖
        (fun y : ℂ => 2*((θ/(‖u‖:ℂ))*y^k+(u/(‖u‖:ℂ))*y).re) z := by
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold scalarOscillatoryPhase
    congr 1
    have he : θ*z^k+u*z = (‖u‖:ℂ)*
        ((θ/(‖u‖:ℂ))*z^k+(u/(‖u‖:ℂ))*z) := by field_simp
    rw [he,Complex.re_ofReal_mul]
    push_cast
    ring
  rw [hi]
  simpa only [abs_of_nonneg (norm_nonneg u)] using hb _ hp ‖u‖

/-- The actual fixed real source factor with an arbitrary power and linear twist. -/
def smoothRealPowerLinearIntegral (k : ℕ) (rho R : ℝ) (θ u : ℝ) : ℂ :=
  realPowerLinearOscillatoryIntegral k (fun x => (positiveSmoothWindow rho R x:ℂ)) θ u

theorem smooth_real_power_linear_nonstationary_bound (k : ℕ) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ u : ℝ,
      |θ| ≤ powerTailRadius k (2*R)*|u| →
      |u|^n*‖smoothRealPowerLinearIntegral k rho R θ u‖ ≤ C := by
  apply real_power_linear_nonstationary_bound k
    (Complex.ofRealCLM.contDiff.comp (positiveSmoothWindow_contDiff rho R)) (by positivity)
  intro x hx
  have hn : positiveSmoothWindow rho R x ≠ 0 := by
    intro he
    apply hx
    change (positiveSmoothWindow rho R x:ℂ) = 0
    rw [he]
    rfl
  have hs := positiveSmoothWindow_support hrho hR hn
  simp only [mem_closedBall,Real.dist_eq,sub_zero]
  rw [abs_of_pos (by linarith : 0 < x)]
  exact hs.2.le

/-- The actual fixed complex radial source factor. -/
def smoothComplexPowerLinearIntegral (k : ℕ) (rho R : ℝ) (θ u : ℂ) : ℂ :=
  complexPowerLinearOscillatoryIntegral k
    (fun z => (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ)) θ u

theorem smooth_complex_power_linear_nonstationary_bound (k : ℕ) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ u : ℂ, 1 ≤ ‖u‖ →
      ‖θ‖ ≤ powerTailRadius k (2*R)*‖u‖ →
      ‖u‖^n*‖smoothComplexPowerLinearIntegral k rho R θ u‖ ≤ C := by
  apply complex_power_linear_nonstationary_bound k
    (Complex.ofRealCLM.contDiff.comp
      ((positiveSmoothWindow_contDiff (rho^2) (R^2)).comp complex_normSq_contDiff)) (by positivity)
  intro z hz
  have hn : positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) ≠ 0 := by
    intro he
    apply hz
    change (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ) = 0
    rw [he]
    rfl
  have hs := positiveSmoothWindow_support (sq_pos_of_pos hrho) (sq_pos_of_pos hR) hn
  rw [Complex.normSq_eq_norm_sq] at hs
  simp only [mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg z]

#print axioms real_power_linear_nonstationary_bound
#print axioms complex_power_linear_nonstationary_bound
#print axioms smooth_real_power_linear_nonstationary_bound
#print axioms smooth_complex_power_linear_nonstationary_bound
end WaringSiegel.WSL3
