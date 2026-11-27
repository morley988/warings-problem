import WaringSiegel.WSL4ArchFourthKernel

/-! # Integrable product arc kernels and quantitative product-region volume

An epsilon of integrable product decay absorbs the logarithmic loss, so the
proof needs no informal conversion to independent radial variables.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure Module NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ENNReal nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem max_norm_rpow_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [IsAddHaarMeasure (volume : Measure E)]
    (s : ℝ) (hs : (finrank ℝ E:ℝ) < s) :
    Integrable (fun x : E => (max 1 ‖x‖)^(-s)) := by
  have hs0 : 0 ≤ s := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg _) hs)
  apply ((integrable_one_add_norm hs).const_mul ((2:ℝ)^s)).mono'
  · exact ((continuous_const.max continuous_norm).rpow_const
      (fun x => Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖))))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)]
    have hmax : (1+‖x‖)/2 ≤ max 1 ‖x‖ := by
      have h1 := le_max_left (1:ℝ) ‖x‖
      have h2 := le_max_right (1:ℝ) ‖x‖
      linarith
    apply (Real.rpow_le_rpow_of_nonpos (by positivity) hmax (neg_nonpos.mpr hs0)).trans_eq
    rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),
      div_inv_eq_mul,mul_comm]

theorem productArcWeight_rpow_places (s : ℝ) (θ : mixedSpace K) :
    (productArcWeight 1 θ)^s =
      (∏ w : {w : InfinitePlace K // IsReal w}, (max 1 ‖θ.1 w‖)^s) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (max 1 ‖θ.2 w‖)^(2*s) := by
  rw [productArcWeight,← Real.finset_prod_rpow _ _
    (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) s,
    InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isReal w.property,mult_isReal,pow_one,one_mul]
  · apply Finset.prod_congr rfl
    intro w hw
    rw [normAtPlace_apply_of_isComplex w.property,mult_isComplex,one_mul,
      ← Real.rpow_natCast,← Real.rpow_mul (le_trans zero_le_one (le_max_left _ _))]
    norm_num

theorem productArcWeight_neg_rpow_integrable (s : ℝ) (hs : 1 < s) :
    Integrable (fun θ : mixedSpace K => (productArcWeight 1 θ)^(-s)) := by
  have hr : Integrable (fun x : ℝ => (max 1 ‖x‖)^(-s)) :=
    max_norm_rpow_integrable s (by simpa using hs)
  have hc : Integrable (fun x : ℂ => (max 1 ‖x‖)^(-(2*s))) :=
    max_norm_rpow_integrable (2*s) (by simpa only [Complex.finrank_real_complex,Nat.cast_ofNat] using
      (show (2:ℝ)<2*s by linarith))
  have hrr := Integrable.fintype_prod (ι := {w : InfinitePlace K // IsReal w}) (fun _ => hr)
  have hcc := Integrable.fintype_prod (ι := {w : InfinitePlace K // IsComplex w}) (fun _ => hc)
  have he : (fun θ : mixedSpace K => (productArcWeight 1 θ)^(-s)) =
      fun θ => (∏ w : {w : InfinitePlace K // IsReal w}, (max 1 ‖θ.1 w‖)^(-s)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (max 1 ‖θ.2 w‖)^(-(2*s)) := by
    funext θ
    rw [productArcWeight_rpow_places]
    simp only [mul_neg]
  rw [he]
  simpa only [volume_pi] using hrr.mul_prod hcc

theorem productArcWeight_neg_rpow_dual_integrable (s : ℝ) (hs : 1 < s) :
    Integrable (fun θ : mixedSpace K => (productArcWeight 1 θ)^(-s))
      (archimedeanDualMeasure (integerLatticeSourceScale K)) :=
  (productArcWeight_neg_rpow_integrable s hs).smul_measure ENNReal.ofReal_ne_top

theorem productArcWeight_sublevel_isCompact (L : ℝ) :
    IsCompact {θ : mixedSpace K | productArcWeight 1 θ ≤ L} := by
  apply (isCompact_closedBall (0:mixedSpace K) L).of_isClosed_subset
    (isClosed_le (productArcWeight_continuous 1) continuous_const)
  intro θ hθ
  rw [Metric.mem_closedBall,dist_zero_right,mixed_norm_le_iff]
  intro w
  have hw : normAtPlace w θ ≤ productArcWeight 1 θ := by
    simpa only [one_mul] using place_le_productArcWeight 1 θ w
  exact hw.trans hθ

/-- Quantitative product-region estimate, with a constant uniform in the
nonnegative growth exponent and the cutoff. -/
theorem productArcWeight_sublevel_integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a L : ℝ), 0 ≤ a → 1 ≤ L →
      (∫ θ in {θ : mixedSpace K | productArcWeight 1 θ ≤ L}, (productArcWeight 1 θ)^a) ≤
        C*L^(a+1+ε) := by
  let f : mixedSpace K → ℝ := fun θ => (productArcWeight 1 θ)^(-(1+ε))
  have hfi : Integrable f := productArcWeight_neg_rpow_integrable (1+ε) (by linarith)
  let C := (∫ θ, f θ)+1
  have hC : 0 < C := by
    have hh : 0 ≤ ∫ θ, f θ := integral_nonneg (fun θ => Real.rpow_nonneg (productArcWeight_pos _ _).le _)
    dsimp [C]
    linarith
  refine ⟨C,hC,fun a L ha hL => ?_⟩
  let S := {θ : mixedSpace K | productArcWeight 1 θ ≤ L}
  have hS := productArcWeight_sublevel_isCompact (K:=K) L
  have hc : Continuous (fun θ : mixedSpace K => (productArcWeight 1 θ)^a) :=
    (productArcWeight_continuous 1).rpow_const (fun θ => Or.inl (productArcWeight_pos _ _).ne')
  have hL0 : 0 < L := by linarith
  have hp : 0 ≤ a+1+ε := by linarith
  have hpoint (θ : mixedSpace K) (hθ : θ ∈ S) :
      (productArcWeight 1 θ)^a ≤ L^(a+1+ε)*f θ := by
    have hA := productArcWeight_pos 1 θ
    have h := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hA.le hθ hp)
      (Real.rpow_nonneg hA.le (-(1+ε)))
    have he : (productArcWeight 1 θ)^(a+1+ε)*(productArcWeight 1 θ)^(-(1+ε)) =
        (productArcWeight 1 θ)^a := by
      rw [← Real.rpow_add hA]
      congr 1
      ring
    rw [he] at h
    exact h
  calc
    _ ≤ ∫ θ in S, L^(a+1+ε)*f θ := setIntegral_mono_on
      (hc.continuousOn.integrableOn_compact hS) (hfi.const_mul _).integrableOn hS.measurableSet hpoint
    _ ≤ ∫ θ, L^(a+1+ε)*f θ := setIntegral_le_integral (hfi.const_mul _)
      (Filter.Eventually.of_forall (fun θ => mul_nonneg (Real.rpow_nonneg hL0.le _)
        (Real.rpow_nonneg (productArcWeight_pos _ _).le _)))
    _ = L^(a+1+ε)*(∫ θ, f θ) := integral_const_mul _ _
    _ ≤ C*L^(a+1+ε) := by dsimp [C]; nlinarith [Real.rpow_nonneg hL0.le (a+1+ε)]

/-- The exponent used by the enlarged-major mixed-sixth tail. -/
theorem productArcWeight_thirteen_sixths_integral_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (∫ θ in {θ : mixedSpace K | productArcWeight 1 θ ≤ L},
        (productArcWeight 1 θ)^((13:ℝ)/6)) ≤ C*L^((19:ℝ)/6+ε) := by
  obtain ⟨C,hC,hb⟩ := productArcWeight_sublevel_integral_bound (K:=K) ε hε
  refine ⟨C,hC,fun L hL => ?_⟩
  simpa only [show (13:ℝ)/6+1=19/6 by norm_num] using hb (13/6) L (by norm_num) hL

#print axioms productArcWeight_neg_rpow_dual_integrable
#print axioms productArcWeight_sublevel_integral_bound
#print axioms productArcWeight_thirteen_sixths_integral_bound
end WaringSiegel.WSL4
