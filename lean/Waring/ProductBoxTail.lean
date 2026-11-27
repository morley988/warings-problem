import Waring.ProductBoxMainScale

/-! # Uniform truncation of the real singular integral -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Waring.ProductBox

def mixedKernelTail (k u v L : ℕ) (N : ℝ) : ℝ :=
  ∫ β in (Set.Icc (-N) N)ᶜ,‖mixedKernel k u v L β‖

theorem mixedKernelTail_nonneg (k u v L : ℕ) (N : ℝ) : 0≤mixedKernelTail k u v L N :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem mixedKernelTail_tendsto_zero (k u v L : ℕ) (hk : 1≤k)
    (hgap : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) :
    Tendsto (fun N : ℕ => mixedKernelTail k u v (L+1) N) atTop (𝓝 0) := by
  let S : ℕ → Set ℝ := fun N => (Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ
  have hanti : Antitone S := by
    intro x y hxy
    exact Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (neg_le_neg (Nat.cast_le.mpr hxy)) (Nat.cast_le.mpr hxy))
  have hempty : (⋂ N : ℕ,S N)=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hn := Set.mem_iInter.mp hx ⌈|x|⌉₊
    exact hn (abs_le.mp (Nat.le_ceil |x|))
  have hsm : ∀ N : ℕ,MeasurableSet (S N) := by
    intro N
    change MeasurableSet ((Set.Icc (-(N : ℝ)) (N : ℝ))ᶜ)
    exact measurableSet_Icc.compl
  have hfi : ∃ N : ℕ,IntegrableOn (fun β => ‖mixedKernel k u v (L+1) β‖) (S N) :=
    ⟨0,(integrable_mixedKernel k u v L hk hgap).norm.integrableOn⟩
  have ht := tendsto_setIntegral_of_antitone (ι := ℕ)
    (f := fun β : ℝ => ‖mixedKernel k u v (L+1) β‖)
    (μ := (volume : Measure ℝ)) (s := S) hsm hanti hfi
  rw [hempty,setIntegral_empty] at ht
  exact ht

theorem singularIntegral_truncation_bound (k u v L : ℕ) (hk : 1≤k)
    (hgap : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) (θ : ℝ) {N : ℝ} (hN : 0≤N) :
    ‖(∫ β : ℝ,singularIntegrand k u v (L+1) θ β)-
        ∫ β in -N..N,singularIntegrand k u v (L+1) θ β‖≤mixedKernelTail k u v (L+1) N := by
  have hi := integrable_singularIntegrand k u v L hk hgap θ
  rw [intervalIntegral.integral_of_le (by linarith : -N≤N),← integral_Icc_eq_integral_Ioc]
  rw [← integral_add_compl measurableSet_Icc hi,add_sub_cancel_left]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards with β
  exact norm_singularIntegrand k u v (L+1) θ β

theorem singularIntegral_uniform_truncation (k u v L : ℕ) (hk : 1≤k)
    (hgap : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ θ : ℝ,
      ‖(∫ β : ℝ,singularIntegrand k u v (L+1) θ β)-
          ∫ β in -(N : ℝ)..(N : ℝ),singularIntegrand k u v (L+1) θ β‖<ε := by
  have ht := (tendsto_order.mp (mixedKernelTail_tendsto_zero k u v L hk hgap)).2 ε hε
  filter_upwards [ht] with N htail θ
  exact (singularIntegral_truncation_bound k u v L hk hgap θ (Nat.cast_nonneg N)).trans_lt htail

#print axioms mixedKernelTail_tendsto_zero
#print axioms singularIntegral_uniform_truncation
end Waring.ProductBox
