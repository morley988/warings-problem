import WaringSiegel.WSL4ArchBump
import WaringSiegel.WSL3UnitCubicStationaryProduct

/-! # Literal place factorization and stationary decay of the near-zero product source -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped NumberField BigOperators Classical ContDiff ComplexConjugate
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL4
open WSL3
set_option maxHeartbeats 1000000

def nearZeroRealCubicKernel (theta u x : ℝ) : ℂ :=
  (realNearZeroBump x:ℂ)*Complex.exp (2*Real.pi*Complex.I*(theta*x^3+u*x:ℝ))
def nearZeroComplexCubicKernel (theta u z : ℂ) : ℂ :=
  (complexNearZeroBump z:ℂ)*Complex.exp (2*Real.pi*Complex.I*(2*(theta*z^3+u*z).re:ℝ))
def nearZeroRealCubicIntegral (theta u : ℝ) : ℂ := ∫ x, nearZeroRealCubicKernel theta u x
def nearZeroComplexCubicIntegral (theta u : ℂ) : ℂ := ∫ z, nearZeroComplexCubicKernel theta u z

theorem nearZeroRealCubicIntegral_eq (theta u : ℝ) :
    nearZeroRealCubicIntegral theta u =
      realCubicTraceIntegral (fun x => (realNearZeroBump x:ℂ)) theta u := by
  apply integral_congr_ae
  filter_upwards [] with x
  unfold nearZeroRealCubicKernel
  congr 1
  congr 1
  push_cast
  ring

theorem nearZeroComplexCubicIntegral_eq (theta u : ℂ) :
    nearZeroComplexCubicIntegral theta u =
      complexCubicTraceIntegral (fun z => (complexNearZeroBump z:ℂ)) theta u := by
  apply integral_congr_ae
  filter_upwards [] with z
  unfold nearZeroComplexCubicKernel
  congr 1
  congr 1
  have he : (2*Real.pi:ℂ)*theta*z^3+(2*Real.pi:ℂ)*u*z =
      ((2*Real.pi:ℝ):ℂ)*(theta*z^3+u*z) := by push_cast; ring
  rw [he]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.im_ofNat,
    zero_mul,mul_zero,sub_zero]
  push_cast
  ring

theorem nearZeroRealCubicIntegral_stationary :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℝ,
      (1+|theta|)^((1:ℝ)/3)*‖nearZeroRealCubicIntegral theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := real_cubic_trace_stationary_bound
    (Complex.ofRealCLM.contDiff.comp realNearZeroBump_contDiff)
    (by norm_num : (0:ℝ) ≤ 1) realNearZeroBump_complex_support
  exact ⟨C,hC,fun theta u => by rw [nearZeroRealCubicIntegral_eq]; exact hb theta u⟩

theorem nearZeroComplexCubicIntegral_stationary :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : ℂ,
      (1+‖theta‖)^((2:ℝ)/3)*‖nearZeroComplexCubicIntegral theta u‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := complex_cubic_trace_stationary_bound
    (Complex.ofRealCLM.contDiff.comp complexNearZeroBump_contDiff)
    complexNearZeroBump_norm_le (by norm_num : (0:ℝ) ≤ 1) complexNearZeroBump_complex_support
  exact ⟨C,hC,fun theta u => by rw [nearZeroComplexCubicIntegral_eq]; exact hb theta u⟩

variable {K : Type*} [Field K] [NumberField K]

def nearZeroCubicLinearIntegral (theta u : mixedSpace K) : ℂ :=
  ∫ x, nearZeroWeight x •
    (archimedeanTraceCharacter theta (x^3)*archimedeanTraceCharacter u x)

theorem nearZeroCubicLinearKernel_product (theta u x : mixedSpace K) :
    nearZeroWeight x •
      (archimedeanTraceCharacter theta (x^3)*archimedeanTraceCharacter u x) =
      (∏ w : {w : InfinitePlace K // IsReal w},
        nearZeroRealCubicKernel (theta.1 w) (u.1 w) (x.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        nearZeroComplexCubicKernel (theta.2 w) (u.2 w) (x.2 w) := by
  rw [cubicTracePhase_product,Complex.real_smul,nearZeroWeight,
    Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_prod]
  simp only [nearZeroRealCubicKernel,nearZeroComplexCubicKernel,Finset.prod_mul_distrib]
  ring

/-- Fubini on the explicitly factored near-zero source. -/
theorem nearZeroCubicLinearIntegral_product (theta u : mixedSpace K) :
    nearZeroCubicLinearIntegral theta u =
      (∏ w : {w : InfinitePlace K // IsReal w}, nearZeroRealCubicIntegral (theta.1 w) (u.1 w)) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, nearZeroComplexCubicIntegral (theta.2 w) (u.2 w) := by
  calc
    _ = ∫ x : mixedSpace K,
        (∏ w : {w : InfinitePlace K // IsReal w},
          nearZeroRealCubicKernel (theta.1 w) (u.1 w) (x.1 w)) *
        ∏ w : {w : InfinitePlace K // IsComplex w},
          nearZeroComplexCubicKernel (theta.2 w) (u.2 w) (x.2 w) :=
      integral_congr_ae (Eventually.of_forall (nearZeroCubicLinearKernel_product theta u))
    _ = _ := by
      rw [Measure.volume_eq_prod,integral_prod_mul
        (fun xr : ({w : InfinitePlace K // IsReal w} → ℝ) =>
          ∏ w, nearZeroRealCubicKernel (theta.1 w) (u.1 w) (xr w))
        (fun xc : ({w : InfinitePlace K // IsComplex w} → ℂ) =>
          ∏ w, nearZeroComplexCubicKernel (theta.2 w) (u.2 w) (xc w)),
        integral_fintype_prod_volume_eq_prod,integral_fintype_prod_volume_eq_prod]
      rfl

/-- The literal product source has exponent d_v/3 at every archimedean place. -/
theorem nearZeroCubicLinearIntegral_stationary :
    ∃ C : ℝ, 0 < C ∧ ∀ theta u : mixedSpace K,
      cubicProductFrequencyWeight (1/3) theta * ‖nearZeroCubicLinearIntegral theta u‖ ≤ C := by
  obtain ⟨Cr,hCr,hr⟩ := nearZeroRealCubicIntegral_stationary
  obtain ⟨Cc,hCc,hc⟩ := nearZeroComplexCubicIntegral_stationary
  refine ⟨(∏ _ : {w : InfinitePlace K // IsReal w}, Cr) *
      (∏ _ : {w : InfinitePlace K // IsComplex w}, Cc),
    mul_pos (Finset.prod_pos (fun _ _ => hCr)) (Finset.prod_pos (fun _ _ => hCc)),
    fun theta u => ?_⟩
  rw [nearZeroCubicLinearIntegral_product,norm_mul,norm_prod,norm_prod]
  have he : cubicProductFrequencyWeight (1/3) theta *
      ((∏ w : {w : InfinitePlace K // IsReal w}, ‖nearZeroRealCubicIntegral (theta.1 w) (u.1 w)‖) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, ‖nearZeroComplexCubicIntegral (theta.2 w) (u.2 w)‖) =
      (∏ w : {w : InfinitePlace K // IsReal w},
        (1+|theta.1 w|)^((1:ℝ)/3)*‖nearZeroRealCubicIntegral (theta.1 w) (u.1 w)‖) *
      ∏ w : {w : InfinitePlace K // IsComplex w},
        (1+‖theta.2 w‖)^((2:ℝ)/3)*‖nearZeroComplexCubicIntegral (theta.2 w) (u.2 w)‖ := by
    simp only [cubicProductFrequencyWeight,Finset.prod_mul_distrib]
    norm_num
    ring
  rw [he]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => by positivity) (fun w _ => hr _ _)
  · exact Finset.prod_le_prod (fun _ _ => by positivity) (fun w _ => hc _ _)
  · exact Finset.prod_nonneg (fun _ _ => by positivity)
  · exact (Finset.prod_pos (fun _ _ => hCr)).le

#print axioms nearZeroCubicLinearIntegral_product
#print axioms nearZeroCubicLinearIntegral_stationary
end WaringSiegel.WSL4

