import WaringSiegel.WSL3UnitPowerDecay

/-!
# Actual all-degree product-place rapid decay of the smooth root integral
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
set_option maxHeartbeats 1000000

def realPlacePowerKernel (k : ℕ) (rho R theta x : ℝ) : ℂ :=
  (positiveSmoothWindow rho R x:ℂ)*Complex.exp (2*Real.pi*Complex.I*(theta*x^k:ℝ))

def complexPlacePowerKernel (k : ℕ) (rho R : ℝ) (theta z : ℂ) : ℂ :=
  (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ)*
    Complex.exp (2*Real.pi*Complex.I*(2*(theta*z^k).re:ℝ))

def realPlacePowerIntegral (k : ℕ) (rho R theta : ℝ) : ℂ :=
  ∫ x, realPlacePowerKernel k rho R theta x

def complexPlacePowerIntegral (k : ℕ) (rho R : ℝ) (theta : ℂ) : ℂ :=
  ∫ z, complexPlacePowerKernel k rho R theta z

theorem realPlacePowerIntegral_rescale (k : ℕ) (rho R theta : ℝ) :
    realPlacePowerIntegral k rho R theta = realPowerOscillatoryIntegral k
      (fun x => (positiveSmoothWindow rho R x:ℂ)) (2*Real.pi*theta) := by
  apply integral_congr_ae
  filter_upwards [] with x
  unfold realPlacePowerKernel
  congr 1
  congr 1
  push_cast
  ring

theorem complexPlacePowerIntegral_rescale (k : ℕ) (rho R : ℝ) (theta : ℂ) :
    complexPlacePowerIntegral k rho R theta = complexPowerOscillatoryIntegral k
      (fun z => (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ))
      ((2*Real.pi:ℂ)*theta) := by
  apply integral_congr_ae
  filter_upwards [] with z
  unfold complexPlacePowerKernel
  congr 1
  congr 1
  have he : (2*Real.pi:ℂ)*theta*z^k = ((2*Real.pi:ℝ):ℂ)*(theta*z^k) := by push_cast; ring
  rw [he,Complex.re_ofReal_mul]
  push_cast
  ring

theorem realPlacePowerIntegral_rapid_bound (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℝ,
      (1+|theta|)^n*‖realPlacePowerIntegral k rho R theta‖ ≤ C := by
  have hs : support (fun x => (positiveSmoothWindow rho R x:ℂ)) ⊆ Set.Icc (rho/2) (2*R) := by
    intro x hx
    have hn : positiveSmoothWindow rho R x ≠ 0 := by
      intro he
      apply hx
      change (positiveSmoothWindow rho R x:ℂ) = 0
      rw [he]
      rfl
    exact ⟨(positiveSmoothWindow_support hrho hR hn).1.le,
      (positiveSmoothWindow_support hrho hR hn).2.le⟩
  obtain ⟨C,hC,hb⟩ := real_power_one_add_rapid_bound k hk
    (Complex.ofRealCLM.contDiff.comp (positiveSmoothWindow_contDiff rho R))
    (by positivity : 0 < rho/2) hs n
  refine ⟨C,hC,fun theta => ?_⟩
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have ht : 1+|theta| ≤ 1+|2*Real.pi*theta| := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    nlinarith [abs_nonneg theta]
  rw [realPlacePowerIntegral_rescale]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht n)
    (norm_nonneg _)).trans (hb _)

theorem complexPlacePowerIntegral_rapid_bound (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : ℂ,
      (1+‖theta‖)^n*‖complexPlacePowerIntegral k rho R theta‖ ≤ C := by
  have hs : support (fun z => (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ)) ⊆
      complexSourceAnnulus (rho/2) (2*R) := by
    intro z hz
    have hn : positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z) ≠ 0 := by
      intro he
      apply hz
      change (positiveSmoothWindow (rho^2) (R^2) (Complex.normSq z):ℂ) = 0
      rw [he]
      rfl
    have hb := positiveSmoothWindow_support (sq_pos_of_pos hrho) (sq_pos_of_pos hR) hn
    rw [Complex.normSq_eq_norm_sq] at hb
    constructor
    · simp only [mem_closedBall,dist_zero_right]
      nlinarith [norm_nonneg z]
    · change rho/2 ≤ ‖z‖
      nlinarith [norm_nonneg z]
  obtain ⟨C,hC,hb⟩ := complex_power_one_add_rapid_bound k hk
    (Complex.ofRealCLM.contDiff.comp
      ((positiveSmoothWindow_contDiff (rho^2) (R^2)).comp complex_normSq_contDiff))
    (by positivity : 0 < rho/2) hs n
  refine ⟨C,hC,fun theta => ?_⟩
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hn : ‖(2*Real.pi:ℂ)*theta‖ = (2*Real.pi)*‖theta‖ := by
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have ht : 1+‖theta‖ ≤ 1+‖(2*Real.pi:ℂ)*theta‖ := by rw [hn]; nlinarith [norm_nonneg theta]
  rw [complexPlacePowerIntegral_rescale]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht n)
    (norm_nonneg _)).trans (hb _)

variable {K : Type*} [Field K] [NumberField K]

theorem powerTracePhase_product (k : ℕ) (theta x : mixedSpace K) :
    archimedeanTraceCharacter theta (x^k) =
      (∏ w : {w : InfinitePlace K // IsReal w},
        Complex.exp (2*Real.pi*Complex.I*(theta.1 w*(x.1 w)^k:ℝ))) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        Complex.exp (2*Real.pi*Complex.I*(2*(theta.2 w*(x.2 w)^k).re:ℝ)) := by
  rw [archimedeanTraceCharacter,archimedeanTrace_eq_sum_real_complex]
  have hxr : (x^k).1 = fun w => (x.1 w)^k := rfl
  have hxc : (x^k).2 = fun w => (x.2 w)^k := rfl
  simp only [Prod.fst_mul,Pi.mul_apply,Prod.snd_mul,hxr,hxc]
  have he : 2*Real.pi*Complex.I*((
      (∑ w : {w : InfinitePlace K // IsReal w}, theta.1 w*(x.1 w)^k) +
        2*(∑ w, (theta.2 w*(x.2 w)^k).re):ℝ):ℂ) =
      (∑ w, 2*Real.pi*Complex.I*(theta.1 w*(x.1 w)^k:ℝ)) +
        ∑ w, 2*Real.pi*Complex.I*(2*(theta.2 w*(x.2 w)^k).re:ℝ) := by
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sum,
      Complex.ofReal_ofNat,mul_add,Finset.mul_sum]
  rw [he,Complex.exp_add,Complex.exp_sum,Complex.exp_sum]

theorem smoothPowerKernel_product (k : ℕ) (rho R : ℝ) (theta x : mixedSpace K) :
    smoothRootWeight rho R x • archimedeanTraceCharacter theta (x^k) =
      (∏ w : {w : InfinitePlace K // IsReal w}, realPlacePowerKernel k rho R (theta.1 w) (x.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlacePowerKernel k rho R (theta.2 w) (x.2 w) := by
  rw [powerTracePhase_product,Complex.real_smul,smoothRootWeight,
    Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_prod]
  simp only [realPlacePowerKernel,complexPlacePowerKernel,Finset.prod_mul_distrib]
  ring

theorem weightedRootIntegral_product (k : ℕ) (rho R : ℝ) (theta : mixedSpace K) :
    weightedRootIntegral k (smoothRootWeight rho R) theta =
      (∏ w : {w : InfinitePlace K // IsReal w}, realPlacePowerIntegral k rho R (theta.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlacePowerIntegral k rho R (theta.2 w) := by
  calc
    _ = ∫ x : mixedSpace K,
        (∏ w : {w : InfinitePlace K // IsReal w}, realPlacePowerKernel k rho R (theta.1 w) (x.1 w)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, complexPlacePowerKernel k rho R (theta.2 w) (x.2 w) :=
      integral_congr_ae (Eventually.of_forall (smoothPowerKernel_product k rho R theta))
    _ = _ := by
      rw [Measure.volume_eq_prod,integral_prod_mul
        (fun xr : ({w : InfinitePlace K // IsReal w} → ℝ) =>
          ∏ w, realPlacePowerKernel k rho R (theta.1 w) (xr w))
        (fun xc : ({w : InfinitePlace K // IsComplex w} → ℂ) =>
          ∏ w, complexPlacePowerKernel k rho R (theta.2 w) (xc w)),
        integral_fintype_prod_volume_eq_prod,integral_fintype_prod_volume_eq_prod]
      rfl

def powerProductFrequencyWeight (n : ℕ) (theta : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // IsReal w}, (1+|theta.1 w|)^n) *
    ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖theta.2 w‖)^n

theorem powerProductFrequencyWeight_pos (n : ℕ) (theta : mixedSpace K) :
    0 < powerProductFrequencyWeight n theta := by
  exact mul_pos (Finset.prod_pos (fun _ _ => by positivity)) (Finset.prod_pos (fun _ _ => by positivity))

/-- Every positive degree has arbitrary product-place rapid frequency
decay for the exact smooth root integral. No Fourier hypothesis is assumed. -/
theorem weightedRootIntegral_product_rapid_bound (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : mixedSpace K,
      powerProductFrequencyWeight n theta*‖weightedRootIntegral k (smoothRootWeight rho R) theta‖ ≤ C := by
  obtain ⟨Cr,hCr,hr⟩ := realPlacePowerIntegral_rapid_bound k hk rho R hrho hR n
  obtain ⟨Cc,hCc,hc⟩ := complexPlacePowerIntegral_rapid_bound k hk rho R hrho hR n
  refine ⟨(∏ _ : {w : InfinitePlace K // IsReal w}, Cr)*
      (∏ _ : {w : InfinitePlace K // IsComplex w}, Cc),
    mul_pos (Finset.prod_pos (fun _ _ => hCr)) (Finset.prod_pos (fun _ _ => hCc)),fun theta => ?_⟩
  rw [weightedRootIntegral_product,norm_mul,norm_prod,norm_prod]
  have he : powerProductFrequencyWeight n theta*
      ((∏ w : {w : InfinitePlace K // IsReal w}, ‖realPlacePowerIntegral k rho R (theta.1 w)‖)*
        ∏ w : {w : InfinitePlace K // IsComplex w}, ‖complexPlacePowerIntegral k rho R (theta.2 w)‖) =
      (∏ w : {w : InfinitePlace K // IsReal w}, (1+|theta.1 w|)^n*
        ‖realPlacePowerIntegral k rho R (theta.1 w)‖)*
      ∏ w : {w : InfinitePlace K // IsComplex w}, (1+‖theta.2 w‖)^n*
        ‖complexPlacePowerIntegral k rho R (theta.2 w)‖ := by
    simp only [powerProductFrequencyWeight,Finset.prod_mul_distrib]
    ring
  rw [he]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg (by positivity) (norm_nonneg _)) (fun w _ => hr _)
  · exact Finset.prod_le_prod (fun w _ => mul_nonneg (by positivity) (norm_nonneg _)) (fun w _ => hc _)
  · exact Finset.prod_nonneg (fun w _ => mul_nonneg (by positivity) (norm_nonneg _))
  · exact (Finset.prod_pos (fun _ _ => hCr)).le

theorem weightedRootIntegral_product_rapid (k : ℕ) (hk : 0 < k) (rho R : ℝ)
    (hrho : 0 < rho) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ theta : mixedSpace K,
      ‖weightedRootIntegral k (smoothRootWeight rho R) theta‖ ≤ C/powerProductFrequencyWeight n theta := by
  obtain ⟨C,hC,hb⟩ := weightedRootIntegral_product_rapid_bound (K := K) k hk rho R hrho hR n
  exact ⟨C,hC,fun theta => (le_div_iff₀ (powerProductFrequencyWeight_pos n theta)).mpr
    (by simpa only [mul_comm] using hb theta)⟩

#print axioms weightedRootIntegral_product
#print axioms weightedRootIntegral_product_rapid
end WaringSiegel.WSL3
