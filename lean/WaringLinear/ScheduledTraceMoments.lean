import WaringDualEnvelope.FiniteOrders
import WaringLinear.SeveralFactorDefect

/-! # From a scheduled defect to a loss-free moment on the trace torus -/
noncomputable section
open MeasureTheory
open scoped NumberField
open WaringSiegel WaringSiegel.WSL2 WaringDualEnvelope

namespace WaringLinear
variable (K : Type*) [Field K] [NumberField K]

/-- Finite weighted supports for each integer scale. The restricted weights
may depend on the scale and on the algebraic integer. -/
structure TraceSumFamily where
  count : ℕ → ℕ
  point : (X : ℕ) → Fin (count X) → 𝓞 K
  small : (X : ℕ) → Fin (count X) → ℝ
  full : (X : ℕ) → Fin (count X) → ℝ
  nonnegative : ∀ X i, 0≤small X i
  nested : ∀ X i, small X i≤full X i

namespace TraceSumFamily
variable {K} (W : TraceSumFamily K)

def restricted (k X : ℕ) := traceWeylSum k (W.point X) (fun i => (W.small X i:ℂ))
def ordinary (k X : ℕ) := traceWeylSum k (W.point X) (fun i => (W.full X i:ℂ))

def admissible (k r : ℕ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ D : ℝ, 0≤D ∧ ∀ X : ℕ, 1≤X →
    (∫ q, ‖W.restricted k X q‖^r ∂traceHaar)≤D*(X:ℝ)^((r:ℝ)-k+k*x+ε)

def minorSaving (k : ℕ) : ℝ := 1/((k:ℝ)*(Real.log k+802113/100000))

/-- For the actual admissibility predicate the allowed epsilon loss is
consumed by the strict minor-arc margin. The resulting moment has no epsilon
in its exponent and its constants apply simultaneously at all scales. -/
theorem loss_free_of_order (k : ℕ) (price : ℝ) (ord : MomentOrder (W.admissible k) k price) :
    ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a:ℕ):ℝ)/k<price ∧
      ∀ (M : ℕ → Set (ArchimedeanTraceTorus K)) (A B C : ℝ),
      (∀ X, MeasurableSet (M X)) → 0≤B → 0≤C →
      (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.restricted k X q‖≤C*X) →
      (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.ordinary k X q‖≤B*(X:ℝ)^(1-minorSaving k)) →
      (∀ X : ℕ, 1≤X → (∫ q in M X, ‖W.ordinary k X q‖^(r+a) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+a-k)) →
      ∃ E : ℝ, ∀ X : ℕ, 1≤X →
        (∫ q, ‖W.restricted k X q‖^(r+a) ∂traceHaar)≤E*(X:ℝ)^((r:ℝ)+a-k) := by
  obtain ⟨r,a,x,er,ea,had,hx,gap,price'⟩ := ord
  cases a with
  | zero =>
    simp only [Nat.cast_zero,zero_div] at gap
    exact False.elim ((not_lt_of_ge (mul_nonneg (Nat.cast_nonneg k) hx)) gap)
  | succ a =>
    refine ⟨r,a+1,er,ea,price',?_⟩
    intro M A B C hM hB hC hbox hminor hmajor
    let ρ := minorSaving k
    let ε := (((a:ℝ)+1)*ρ-k*x)/2
    have hg : k*x<((a:ℝ)+1)*ρ := by
      simpa [ρ,minorSaving,div_eq_mul_inv] using gap
    have hε : 0<ε := by unfold ε;linarith
    obtain ⟨D,hD,hmom⟩ := had ε hε
    obtain ⟨u,hu⟩ := er
    obtain ⟨v,hv⟩ := ea
    have order : r+0+a=2*(u+v-1)+1 := by omega
    refine ⟨2*((2:ℝ)^(r+(a+1))*A+B^(a+1)*D),?_⟩
    intro X hX
    have hbound := trace_loss_free_several_factors k (W.point X) (W.small X) (W.full X)
      (W.nonnegative X) (W.nested X) (u+v-1) r 0 a order (M X) (hM X) X C B A D ρ
      (k*x+ε) (by exact_mod_cast hX) hC hB hD (by unfold ε;linarith)
      (hbox X hX) (hminor X hX)
      (by simpa [ordinary,Nat.add_assoc,add_assoc] using hmajor X hX)
      (by simpa [restricted,add_assoc] using hmom X hX)
    simpa [restricted,add_assoc] using hbound

#print axioms loss_free_of_order
end TraceSumFamily
end WaringLinear
