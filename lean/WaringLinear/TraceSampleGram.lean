import WaringLinear.TraceConductorStage
import WaringSiegel.WSL3PoissonMixedTrivial
import WaringLinear.GramAtThreshold
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Actual trace Fourier rows for the number-field large-value stage -/
noncomputable section
open WaringSiegel WaringSiegel.WSL3Poisson
open scoped BigOperators Classical ComplexConjugate NumberField
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

private abbrev tracePhase (n : 𝓞 K) (k : ℕ) (x : ArchimedeanTraceTorus K) := traceTorusCharacter (n^k) x

def traceSupportSum (s : Finset (𝓞 K)) (k:ℕ) (x:ArchimedeanTraceTorus K) :=
  ∑n∈s,tracePhase n k x

theorem traceSupportSum_asWeyl (s:Finset (𝓞 K)) (k:ℕ) (x:ArchimedeanTraceTorus K) :
    traceSupportSum s k x=traceWeylSum k (fun n:s=>n.val) (fun _=>1) x := by
  rw [traceWeylSum]
  simp only [one_mul]
  exact (Finset.sum_coe_sort s (fun n => traceTorusCharacter (n^k) x)).symm

private theorem tracePhase_neg (n : 𝓞 K) (k:ℕ) (x:ArchimedeanTraceTorus K) :
    tracePhase n k (-x)=conj (tracePhase n k x) := by
  change (traceTorusAddChar (n^k)) (-x)=_
  rw [AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (traceTorusCharacter_norm_one ..)

/-- The large-value Gram uses the full coprime interval as its Hilbert
coordinate set. Restricting the marked support only changes this coefficient
vector, and therefore leaves all Gram entries complete. -/
def traceHilbertRow (box : Finset (𝓞 K)) (k : ℕ) (a : (ArchimedeanTraceTorus K)) : EuclideanSpace ℂ box :=
  (EuclideanSpace.equiv box ℂ).symm fun n => conj (tracePhase n.1 k a)

def traceHilbertCoefficients (box support : Finset (𝓞 K)) (k : ℕ) (x : (ArchimedeanTraceTorus K)) :
    EuclideanSpace ℂ box :=
  (EuclideanSpace.equiv box ℂ).symm fun n => if n.1∈support then tracePhase n.1 k x else 0

theorem trace_coeff_norm_sq (box support : Finset (𝓞 K)) (k : ℕ) (x : (ArchimedeanTraceTorus K)) :
    ‖traceHilbertCoefficients box support k x‖^2 ≤ box.card := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _n:box,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n.1∈support <;> simp [traceHilbertCoefficients,hn,tracePhase,traceTorusCharacter_norm_one]
    _ = _ := by simp

/-- Fourier samples of any restricted set are correlations of the same
unweighted trace-character row vectors with coefficients of squared norm ≤X. -/
theorem trace_sample_inner (box s : Finset (𝓞 K)) (hs : s⊆box) (k : ℕ) (x a : (ArchimedeanTraceTorus K)) :
    inner ℂ (traceHilbertRow box k a) (traceHilbertCoefficients box s k x) =
      traceSupportSum s k (x+a) := by
  rw [PiLp.inner_apply]
  have H : ∑n:box,(if n.val∈s then tracePhase n.val k (x+a) else 0) =
      traceSupportSum s k (x+a) := by
    rw [Finset.sum_coe_sort box (fun n => if n∈s then tracePhase n k (x+a) else 0),
      ←Finset.sum_filter]
    have e : box.filter (fun n => n∈s)=s := by ext n; simp only [Finset.mem_filter]; tauto_set
    rw [e]
    rfl
  rw [←H]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.1∈s <;> simp [traceHilbertRow,traceHilbertCoefficients,hn,tracePhase,traceTorusCharacter_add,RCLike.inner_apply]

/-- Every Gram matrix entry is the complete polynomial correlation on
the unchanged coprime sampling interval. -/
theorem trace_row_inner (box : Finset (𝓞 K)) (k : ℕ) (a b : (ArchimedeanTraceTorus K)) :
    inner ℂ (traceHilbertRow box k a) (traceHilbertRow box k b) = traceSupportSum box k (a-b) := by
  rw [PiLp.inner_apply]
  unfold traceSupportSum
  rw [←Finset.sum_coe_sort box (fun n => traceTorusCharacter (n^k) (a-b))]
  apply Finset.sum_congr rfl
  intro n _
  change conj (tracePhase n.1 k b) * conj (conj (tracePhase n.1 k a)) = tracePhase n.1 k (a-b)
  rw [sub_eq_add_neg,show tracePhase n.1 k (a+-b)=tracePhase n.1 k a*tracePhase n.1 k (-b) from traceTorusCharacter_add ..,tracePhase_neg,Complex.conj_conj,mul_comm]

theorem trace_sum_norm_le_card (s : Finset (𝓞 K)) (k : ℕ) (x : (ArchimedeanTraceTorus K)) :
    ‖traceSupportSum s k x‖≤s.card := by
  apply (norm_sum_le _ _).trans
  simp [tracePhase,traceTorusCharacter_norm_one]

/-- Complete correlation estimates split into a bounded small-conductor
operator and bounded individual high-conductor entries imply the squared
fibre estimate in the real-moment conductor recursion, at every point of
the actual circle. The fibre is the actual kernel of multiplication by the kth power of the retained algebraic integer. -/
theorem trace_correlation_fibre
    (box s : Finset (𝓞 K)) (hs : s⊆box) (m : 𝓞 K) (hm : m≠0) (k : ℕ)
    (X C E z σ : ℝ) (hX : 1≤X) (hC : 0≤C) (hE : 0≤E) (hz : 0≤z)
    (hc : (box.card:ℝ)≤X) (hslack : 32*E≤X^(σ-2*z))
    (Small Large : (ArchimedeanTraceTorus K)→(ArchimedeanTraceTorus K)→ℂ)
    (hsplit : ∀ a b : (traceTorusMul (m^k)).ker,
      traceSupportSum box k (a.val-b.val)=Small a.val b.val+Large a.val b.val)
    (hsmall : ∀ (t : Finset (traceTorusMul (m^k)).ker) (w : t → ℂ),
      ‖gramForm (fun a b:t => Small a.1.val b.1.val) w‖≤(C*X)*∑i,‖w i‖^2)
    (hlarge : ∀ a b : (traceTorusMul (m^k)).ker, ‖Large a.val b.val‖≤E*X^(1-σ))
    (x : (ArchimedeanTraceTorus K)) : traceFibreMass m hm k ({u:ArchimedeanTraceTorus K | X^(1-z)≤2*‖traceSupportSum s k u‖}.indicator (fun u => ‖traceSupportSum s k u‖^2)) x
       ≤ ((18+8*z*Real.logb 2 X)*C)*X^2 := by
  classical
  letI := traceTorusMul_kernel_finite_type (m^k) (pow_ne_zero _ hm)
  letI := Fintype.ofFinite (traceTorusMul (m^k)).ker
  let v (a : (traceTorusMul (m^k)).ker) := traceHilbertRow box k a.val
  let c := traceHilbertCoefficients box s k x
  have hc' : ‖c‖^2≤X := (trace_coeff_norm_sq box s k x).trans hc
  have upper (i : (traceTorusMul (m^k)).ker) : ‖inner ℂ (v i) c‖≤X := by
    change ‖inner ℂ (traceHilbertRow box k i.val) (traceHilbertCoefficients box s k x)‖≤X
    rw [trace_sample_inner box s hs]
    exact (trace_sum_norm_le_card s k (x+i.val)).trans
      ((Nat.cast_le.mpr (Finset.card_le_card hs)).trans hc)
  have H := gram_fibre_at_amplitude v c X C E z σ hX hC hE hz hc' hslack upper
    (fun t w => synthesis_of_split_gram (fun i:t => v i.val)
      (fun a b:t => Small a.1.val b.1.val) (fun a b:t => Large a.1.val b.1.val)
      (C*X) (E*X^(1-σ)) (fun a b => (trace_row_inner ..).trans (hsplit a.val b.val))
      (hsmall t) (fun a b => hlarge a.val b.val) w)
  apply le_trans (le_of_eq ?_) H
  apply Finset.sum_congr rfl
  intro i _
  change {u : (ArchimedeanTraceTorus K) | X^(1-z)≤2*‖traceSupportSum s k u‖}.indicator _ (x+i.val) =
    {u:ℝ | X^(1-z)/2≤u}.indicator _ ‖inner ℂ (traceHilbertRow box k i.val) (traceHilbertCoefficients box s k x)‖
  rw [trace_sample_inner box s hs]
  by_cases h : X^(1-z)≤2*‖traceSupportSum s k (x+i.val)‖
  · have h' : X^(1-z)/2≤‖traceSupportSum s k (x+i.val)‖ := by linarith
    simp [Set.indicator, h, h']
  · have h' : ¬ X^(1-z)/2≤‖traceSupportSum s k (x+i.val)‖ := by linarith
    simp [Set.indicator,h,h']

#print axioms trace_sample_inner
#print axioms trace_row_inner
#print axioms trace_correlation_fibre
end WaringLinear
