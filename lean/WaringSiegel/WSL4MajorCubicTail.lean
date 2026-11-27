import WaringSiegel.WSL4MajorCubicTailScalar

/-! # Integrated conductor/product-frequency tails for the eight-cube major kernel -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def cubicPruningRegion (q X L C0 : ℝ) : Set (mixedSpace K) :=
  {β | L≤q*productArcWeight 1 β ∧ q*productArcWeight 1 β≤C0*X}

def cubicPruningKernel (q X Y : ℝ) (β : mixedSpace K) : ℝ :=
  (productArcWeight 1 β)^(-(4:ℝ))*(1+Y*q*productArcWeight 1 β/X)^8

theorem cubicPruningRegion_isCompact (q X L C0 : ℝ) (hq : 0<q) :
    IsCompact (cubicPruningRegion (K := K) q X L C0) := by
  have hqA : Continuous (fun β : mixedSpace K => q*productArcWeight 1 β) :=
    continuous_const.mul (productArcWeight_continuous 1)
  have hclosed : IsClosed (cubicPruningRegion (K := K) q X L C0) :=
    (isClosed_le continuous_const hqA).inter (isClosed_le hqA continuous_const)
  apply (productArcWeight_sublevel_isCompact (K := K) (C0*X/q)).of_isClosed_subset hclosed
  intro β hβ
  exact (le_div_iff₀ hq).mpr (by simpa only [mul_comm] using hβ.2)

theorem cubicPruningKernel_continuous (q X Y : ℝ) :
    Continuous (cubicPruningKernel (K := K) q X Y) := by
  apply Continuous.mul
  · exact (productArcWeight_continuous 1).rpow_const
      (fun β => Or.inl (productArcWeight_pos 1 β).ne')
  · exact (continuous_const.add
      ((continuous_const.mul (productArcWeight_continuous 1)).div_const X)).pow 8

theorem cubicPruning_kernel_integral_bound (C0 : ℝ) (hC0 : 1≤C0) :
    ∃ C : ℝ, 0<C ∧ ∀ q X Y L : ℝ, 0<q → 0<X → 0≤Y → 0<L →
      (∫ β in cubicPruningRegion (K := K) q X L C0,cubicPruningKernel q X Y β
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤
      C*q^((5:ℝ)/4)*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by
  let μ : Measure (mixedSpace K) := archimedeanDualMeasure (integerLatticeSourceScale K)
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp only [μ]
    rw [integerLatticeDualMeasure_eq_map]
    infer_instance
  let g : mixedSpace K → ℝ := fun β => (productArcWeight 1 β)^(-(11:ℝ)/4)
  have hgi : Integrable g μ := by
    simpa only [g,μ,neg_div] using productArcWeight_neg_rpow_dual_integrable (K := K)
      (11/4) (by norm_num)
  let J : ℝ := (∫ β,g β ∂μ)+1
  have hJ : 0<J := by
    have hnon : 0≤∫ β,g β ∂μ := integral_nonneg
      (fun β => Real.rpow_nonneg (productArcWeight_pos 1 β).le _)
    dsimp [J]
    linarith
  let D : ℝ := (2:ℝ)^8*C0^((27:ℝ)/4)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨D*J,by positivity,?_⟩
  intro q X Y L hq hX hY hL
  let E : ℝ := 1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)
  have hE : 0≤E := by dsimp [E]; positivity
  let c : ℝ := D*q^((5:ℝ)/4)*E
  have hc : 0≤c := by dsimp [c]; positivity
  have hset := cubicPruningRegion_isCompact (K := K) q X L C0 hq
  have hpoint (β : mixedSpace K) (hβ : β∈cubicPruningRegion (K := K) q X L C0) :
      cubicPruningKernel q X Y β≤c*g β := by
    have h := cubic_pruning_scalar_bound q (productArcWeight 1 β) X Y L C0
      hq (productArcWeight_pos _ _) hX hY hL hC0 hβ.1 hβ.2
    exact h.trans_eq (by dsimp [c,D,E,g,cubicPruningKernel]; ring)
  calc
    _ ≤ ∫ β in cubicPruningRegion (K := K) q X L C0,c*g β ∂μ :=
      setIntegral_mono_on
        ((cubicPruningKernel_continuous (K := K) q X Y).continuousOn.integrableOn_compact hset)
        (hgi.const_mul c).integrableOn hset.measurableSet hpoint
    _ ≤ ∫ β,c*g β ∂μ := setIntegral_le_integral (hgi.const_mul c)
      (Filter.Eventually.of_forall (fun β =>
        mul_nonneg hc (Real.rpow_nonneg (productArcWeight_pos 1 β).le _)))
    _ = c*∫ β,g β ∂μ := integral_const_mul _ _
    _ ≤ c*J := mul_le_mul_of_nonneg_left (by dsimp [J]; linarith) hc
    _ = _ := by dsimp [c,E]; ring

theorem cubicPruning_finite_weighted_bound (C0 : ℝ) (hC0 : 1≤C0) :
    ∃ C : ℝ, 0<C ∧ ∀ {α : Type*} [Fintype α],
      ∀ q w : α → ℝ, (∀ i,0<q i) → (∀ i,0≤w i) →
      ∀ X Y L M : ℝ, 0<X → 0≤Y → 0<L →
      (∑ i,q i^((5:ℝ)/4)*w i)≤M →
      (∑ i,w i*∫ β in cubicPruningRegion (K := K) (q i) X L C0,
        cubicPruningKernel (q i) X Y β
          ∂archimedeanDualMeasure (integerLatticeSourceScale K)) ≤
        C*M*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by
  obtain ⟨C,hC,hbound⟩ := cubicPruning_kernel_integral_bound (K := K) C0 hC0
  refine ⟨C,hC,?_⟩
  intro α _ q w hq hw X Y L M hX hY hL hmass
  let E : ℝ := 1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)
  have hE : 0≤E := by dsimp [E]; positivity
  calc
    _ ≤ ∑ i,w i*(C*q i^((5:ℝ)/4)*E) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (hbound (q i) X Y L (hq i) hX hY hL) (hw i))
    _ = (C*E)*∑ i,q i^((5:ℝ)/4)*w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (C*E)*M := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC.le hE)
    _ = _ := by dsimp [E]; ring

#print axioms cubicPruning_kernel_integral_bound
#print axioms cubicPruning_finite_weighted_bound
end WaringSiegel.WSL4
