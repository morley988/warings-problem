import WaringLinear.ScalarConductorStage
import WaringLinear.GramAtThreshold
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Actual Fourier rows for the scalar large-value stage -/
noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace WaringLinear

private abbrev phase (n k : ℕ) (x : ScalarTorus) := fourier ((n^k:ℕ):ℤ) x
private theorem phase_add (n k : ℕ) (x y : ScalarTorus) :
    phase n k (x+y)=phase n k x*phase n k y := by
  simp only [phase,fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul]

private theorem phase_neg (n k : ℕ) (x : ScalarTorus) :
    phase n k (-x)=conj (phase n k x) := by
  rw [phase,fourier_apply,smul_neg,←neg_smul,←fourier_apply,fourier_neg]

/-- The large-value Gram uses the full coprime interval as its Hilbert
coordinate set. Restricting the marked support only changes this coefficient
vector, and therefore leaves all Gram entries complete. -/
def scalarRow (box : Finset ℕ) (k : ℕ) (a : ScalarTorus) : EuclideanSpace ℂ box :=
  (EuclideanSpace.equiv box ℂ).symm fun n => conj (phase n.1 k a)

def scalarCoefficients (box support : Finset ℕ) (k : ℕ) (x : ScalarTorus) :
    EuclideanSpace ℂ box :=
  (EuclideanSpace.equiv box ℂ).symm fun n => if n.1∈support then phase n.1 k x else 0

private theorem phase_norm (n k : ℕ) (x : ScalarTorus) : ‖phase n k x‖=1 :=
  Circle.norm_coe _

theorem scalar_coeff_norm_sq (box support : Finset ℕ) (k : ℕ) (x : ScalarTorus) :
    ‖scalarCoefficients box support k x‖^2 ≤ box.card := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _n:box,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n.1∈support <;> simp [scalarCoefficients,hn]
    _ = _ := by simp

/-- Fourier samples of any restricted set are correlations of the same
complete, unweighted row vectors with coefficients of squared norm ≤X. -/
theorem scalar_sample_inner (box s : Finset ℕ) (hs : s⊆box) (k : ℕ) (x a : ScalarTorus) :
    inner ℂ (scalarRow box k a) (scalarCoefficients box s k x) =
      scalarPowerSum s k (x+a) := by
  rw [PiLp.inner_apply]
  have H : ∑n:box,(if n.val∈s then phase n.val k (x+a) else 0) =
      scalarPowerSum s k (x+a) := by
    rw [Finset.sum_coe_sort box (fun n => if n∈s then phase n k (x+a) else 0),
      ←Finset.sum_filter]
    have e : box.filter (fun n => n∈s)=s := by ext n; simp only [Finset.mem_filter]; tauto_set
    rw [e]
    rfl
  rw [←H]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.1∈s <;> simp [scalarRow,scalarCoefficients,hn,AddCircle.toCircle_add,Circle.coe_mul,RCLike.inner_apply]

/-- Every Gram matrix entry is the complete polynomial correlation on
the unchanged coprime sampling interval. -/
theorem scalar_row_inner (box : Finset ℕ) (k : ℕ) (a b : ScalarTorus) :
    inner ℂ (scalarRow box k a) (scalarRow box k b) = scalarPowerSum box k (a-b) := by
  rw [PiLp.inner_apply]
  unfold scalarPowerSum
  rw [←Finset.sum_coe_sort box (fun n => fourier ((n^k:ℕ):ℤ) (a-b))]
  apply Finset.sum_congr rfl
  intro n _
  change conj (phase n.1 k b) * conj (conj (phase n.1 k a)) = phase n.1 k (a-b)
  rw [sub_eq_add_neg,phase_add,phase_neg,Complex.conj_conj,mul_comm]

theorem scalar_sum_norm_le_card (s : Finset ℕ) (k : ℕ) (x : ScalarTorus) :
    ‖scalarPowerSum s k x‖≤s.card := by
  apply (norm_sum_le _ _).trans
  simp

/-- Complete correlation estimates split into a bounded small-conductor
operator and bounded individual high-conductor entries imply the squared
fibre estimate in the real-moment conductor recursion, at every point of
the actual circle. No phase or sampled-kernel identity is assumed. -/
theorem classical_correlation_fibre
    (box s : Finset ℕ) (hs : s⊆box) (q k : ℕ) (hq : 0<q)
    (X C E z σ : ℝ) (hX : 1≤X) (hC : 0≤C) (hE : 0≤E) (hz : 0≤z)
    (hc : (box.card:ℝ)≤X) (hslack : 32*E≤X^(σ-2*z))
    (Small Large : ScalarTorus→ScalarTorus→ℂ)
    (hsplit : ∀ a b : (circleCover q).ker,
      scalarPowerSum box k (a.val-b.val)=Small a.val b.val+Large a.val b.val)
    (hsmall : ∀ (t : Finset (circleCover q).ker) (w : t → ℂ),
      ‖gramForm (fun a b:t => Small a.1.val b.1.val) w‖≤(C*X)*∑i,‖w i‖^2)
    (hlarge : ∀ a b : (circleCover q).ker, ‖Large a.val b.val‖≤E*X^(1-σ))
    (x : ScalarTorus) : scalarFibreMass q hq X z (scalarPowerSum s k) x
       ≤ ((18+8*z*Real.logb 2 X)*C)*X^2 := by
  classical
  letI := circleKernelFintype q hq
  let v (a : (circleCover q).ker) := scalarRow box k a.val
  let c := scalarCoefficients box s k x
  have hc' : ‖c‖^2≤X := (scalar_coeff_norm_sq box s k x).trans hc
  have upper (i : (circleCover q).ker) : ‖inner ℂ (v i) c‖≤X := by
    change ‖inner ℂ (scalarRow box k i.val) (scalarCoefficients box s k x)‖≤X
    rw [scalar_sample_inner box s hs]
    exact (scalar_sum_norm_le_card s k (x+i.val)).trans
      ((Nat.cast_le.mpr (Finset.card_le_card hs)).trans hc)
  have H := gram_fibre_at_amplitude v c X C E z σ hX hC hE hz hc' hslack upper
    (fun t w => synthesis_of_split_gram (fun i:t => v i.val)
      (fun a b:t => Small a.1.val b.1.val) (fun a b:t => Large a.1.val b.1.val)
      (C*X) (E*X^(1-σ)) (fun a b => (scalar_row_inner ..).trans (hsplit a.val b.val))
      (hsmall t) (fun a b => hlarge a.val b.val) w)
  apply le_trans (le_of_eq ?_) H
  apply Finset.sum_congr rfl
  intro i _
  change {u : ScalarTorus | X^(1-z)≤2*‖scalarPowerSum s k u‖}.indicator _ (x+i.val) =
    {u:ℝ | X^(1-z)/2≤u}.indicator _ ‖inner ℂ (scalarRow box k i.val) (scalarCoefficients box s k x)‖
  rw [scalar_sample_inner box s hs]
  by_cases h : X^(1-z)≤2*‖scalarPowerSum s k (x+i.val)‖
  · have h' : X^(1-z)/2≤‖scalarPowerSum s k (x+i.val)‖ := by linarith
    simp [Set.indicator, h, h']
  · have h' : ¬ X^(1-z)/2≤‖scalarPowerSum s k (x+i.val)‖ := by linarith
    simp [Set.indicator,h,h']

#print axioms scalar_sample_inner
#print axioms scalar_row_inner
#print axioms classical_correlation_fibre
end WaringLinear
