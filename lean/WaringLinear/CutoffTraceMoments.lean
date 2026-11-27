import WaringLinear.ScheduledTraceMoments
import WaringDualEnvelope.ShorteningOrders

/-! # Choosing the smoothness cutoff after the loss budget -/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2 WaringDualEnvelope WaringEnvelope
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

/-- The normalization k*x is the (unnormalized) excess in the moment.
For each accuracy the constants may depend on the sufficiently small
cutoff chosen after it. -/
def cutoffAdmissible (W : ℝ → TraceSumFamily K) (k r : ℕ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
    ∃ D : ℝ, 0≤D ∧ ∀ X : ℕ, 1≤X →
      (∫ q, ‖(W η).restricted k X q‖^r ∂traceHaar)≤D*(X:ℝ)^((r:ℝ)-k+k*x+ε)

def uniformMomentAt (W : TraceSumFamily K) (k r a : ℕ) : Prop :=
  ∀ (M : ℕ → Set (ArchimedeanTraceTorus K)) (A B C : ℝ),
      (∀ X, MeasurableSet (M X)) → 0≤B → 0≤C →
      (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.restricted k X q‖≤C*X) →
      (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.ordinary k X q‖≤B*(X:ℝ)^(1-TraceSumFamily.minorSaving k)) →
      (∀ X : ℕ, 1≤X → (∫ q in M X, ‖W.ordinary k X q‖^(r+a) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+a-k)) →
      ∃ E : ℝ, ∀ X : ℕ, 1≤X →
        (∫ q, ‖W.restricted k X q‖^(r+a) ∂traceHaar)≤E*(X:ℝ)^((r:ℝ)+a-k)

/-- A strict defect margin fixes one cutoff range at which the absorbed
moment is uniform in scale. -/
theorem cutoff_loss_free_at (W : ℝ → TraceSumFamily K) (k r a : ℕ) (x : ℝ)
    (er : Even r) (ea : Even a) (had : cutoffAdmissible W k r x) (hx : 0≤x)
    (gap : (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000))) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ → uniformMomentAt (W η) k r a := by
  cases a with
  | zero =>
    simp only [Nat.cast_zero,zero_div] at gap
    exact False.elim ((not_lt_of_ge (mul_nonneg (Nat.cast_nonneg k) hx)) gap)
  | succ a =>
    let ρ := TraceSumFamily.minorSaving k
    let ε := (((a:ℝ)+1)*ρ-k*x)/2
    have hg : k*x<((a:ℝ)+1)*ρ := by
      simpa [ρ,TraceSumFamily.minorSaving,div_eq_mul_inv] using gap
    have hε : 0<ε := by unfold ε;linarith
    obtain ⟨η₀,hη₀,hwin⟩ := had ε hε
    refine ⟨η₀,hη₀,?_⟩
    intro η hη hle M A B C hM hB hC hbox hminor hmajor
    obtain ⟨D,hD,hmom⟩ := hwin η hη hle
    obtain ⟨u,hu⟩ := er
    obtain ⟨v,hv⟩ := ea
    have order : r+0+a=2*(u+v-1)+1 := by omega
    refine ⟨2*((2:ℝ)^(r+(a+1))*A+B^(a+1)*D),?_⟩
    intro X hX
    have hbound := trace_loss_free_several_factors k ((W η).point X) ((W η).small X) ((W η).full X)
      ((W η).nonnegative X) ((W η).nested X) (u+v-1) r 0 a order (M X) (hM X) X C B A D ρ
      (k*x+ε) (by exact_mod_cast hX) hC hB hD (by unfold ε;linarith)
      (hbox X hX) (hminor X hX)
      (by simpa [TraceSumFamily.ordinary,Nat.add_assoc,add_assoc] using hmajor X hX)
      (by simpa [TraceSumFamily.restricted,add_assoc] using hmom X hX)
    simpa [TraceSumFamily.restricted,add_assoc] using hbound


/-- At the chosen even order, every sufficiently small fixed cutoff gives
the loss-free moment. Its size is chosen after the strict minor-arc margin. -/
theorem cutoff_linear_loss_free (W : ℝ → TraceSumFamily K) (k : ℕ) (hk : 21≤k)
    (seed : SelectedSeeds (cutoffAdmissible W k) k)
    (step : ShorteningStep DualStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a:ℕ):ℝ)/k<6874/1000 ∧
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ → uniformMomentAt (W η) k r a := by
  obtain ⟨r,a,x,er,ea,had,hx,gap,price⟩ := all_shortening_orders_6874 k hk _ seed step
  exact ⟨r,a,er,ea,price,cutoff_loss_free_at W k r a x er ea had hx gap⟩

#print axioms cutoff_linear_loss_free
end WaringLinear
