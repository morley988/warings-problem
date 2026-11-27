import WaringLinear.EfficientDifferencingSeed
import WaringLinear.SharpTraceMoments
import WaringSiegel.WSL2MomentVinogradov

/-! # The field efficient-differencing input to the all-degree schedule

The first input estimates a finite weighted count of equal sums of powers of
algebraic integers. The second is the shortening estimate for the marked
trace sums. The conductor family is selected by the degree. The derived
moment and the strict residual defect refer to probability Haar measure on
the archimedean trace torus of the same field. -/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2 WaringEnvelope WaringDualEnvelope
open scoped NumberField BigOperators Classical
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

/-- Weighted ordered pairs of s-tuples giving the same sum of kth powers. -/
def TraceSumFamily.powerEnergy (W : TraceSumFamily K) (k s X : ℕ) : ℝ :=
  ∑ t : (Fin s → Fin (W.count X)) × (Fin s → Fin (W.count X)),
    if (∑ i, W.point X (t.1 i)^k) = ∑ i, W.point X (t.2 i)^k then
      (∏ i, W.small X (t.1 i))*(∏ i, W.small X (t.2 i)) else 0

/-- Exact orthogonality, with multiplicities and real weights retained. -/
theorem TraceSumFamily.trace_moment_eq_powerEnergy (W : TraceSumFamily K) (k s X : ℕ) :
    (∫ q, ‖W.restricted k X q‖^(2*s) ∂traceHaar)=W.powerEnergy k s X := by
  rw [TraceSumFamily.restricted,traceWeylSum_integral_norm_pow]
  change (∫ θ, ‖frequencySum (fun i => integerCoordinates K ((W.point X i)^k))
    (fun i => (W.small X i : ℂ)) θ‖^(2*s) ∂latticeHaar)=_
  rw [integral_norm_frequencySum_even]
  unfold TraceSumFamily.powerEnergy
  simp only [←map_sum, (integerCoordinates_injective K).eq_iff, ←Complex.ofReal_prod,
    Complex.conj_ofReal, ←Complex.ofReal_mul, Complex.ofReal_re]

/-- Uniform over scales at every sufficiently small smoothness cutoff, the
finite counting inequality in efficient differencing. Index j=0 is the
second moment. -/
def DifferencingCounts (W : ℝ → TraceSumFamily K) (k : ℕ) : Prop :=
  ∀ j : ℕ, ∀ ε : ℝ, 0<ε → ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
    ∃ D : ℝ, 0≤D ∧ ∀ X : ℕ, 1≤X →
      (W η).powerEnergy k (j+1) X ≤ D*(X:ℝ)^((2*((j:ℝ)+1))-k+edDefect k j+ε)

/-- The exact rounded mean-value seeds follow from the raw algebraic
solution counts; there is no assumed analytic seed at the selected heights. -/
theorem selectedSeeds_of_differencingCounts {W : ℝ → TraceSumFamily K} {k : ℕ}
    (hk : 21≤k) (count : DifferencingCounts W k) :
    SelectedSeeds (cutoffAdmissible W k) k := by
  intro z hlo hhi
  obtain ⟨hr,hd⟩ := edDefect_at_exact_seed k z hk hlo hhi
  let j := edSeedIndex k z
  rw [←hr]
  intro ε hε
  obtain ⟨η₀,h0,h⟩ := count j ε hε
  refine ⟨η₀,h0,?_⟩
  intro η hη hsmall
  obtain ⟨D,hD,estimate⟩ := h η hη hsmall
  refine ⟨D,hD,?_⟩
  intro X hX
  rw [TraceSumFamily.trace_moment_eq_powerEnergy]
  refine (estimate X hX).trans (mul_le_mul_of_nonneg_left ?_ hD)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX)
  push_cast
  change edDefect k j ≤ (k:ℝ)*seedDefect z at hd
  linarith only [hd]

/-- The finite band and the large-degree band use distinct certified
Fourier inequalities. Only the family selected at the degree is used. -/
def fieldConductorStage (k : ℕ) (θ u σ : ℝ) : Prop :=
  if k<180000^2 then DualStage k θ u σ else WaringSharpTail.Branch k θ u σ

theorem field_shortening_orders_of_differencing (W : ℝ → TraceSumFamily K) (k : ℕ)
    (hk : 21≤k) (count : DifferencingCounts W k)
    (shorten : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ cutoffAdmissible W k r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  apply WaringSharp.all_shortening_orders_with_extra_6873 k hk _
    (selectedSeeds_of_differencingCounts hk count)
  · intro small
    simpa only [ShorteningStep,fieldConductorStage,if_pos small] using shorten
  · intro large
    simpa only [ShorteningStep,fieldConductorStage,if_neg (not_lt.mpr large)] using shorten

#print axioms TraceSumFamily.trace_moment_eq_powerEnergy
#print axioms selectedSeeds_of_differencingCounts
#print axioms field_shortening_orders_of_differencing
end WaringLinear
