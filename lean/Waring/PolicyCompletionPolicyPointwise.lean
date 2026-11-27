import Waring.PolicyCompletionResourcePointwise

/-! # One uniform pointwise constant for all pieces of a literal policy -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionPolicyPointwise
open Certificate PolicyCompletionTerminalShape PolicyCompletionResourceActual
open PolicyCompletionResourceFormula PolicyCompletionResourcePointwise PolicyCompletionShapeCap
open PolicyCompletionMajorPowerRanges PolicyCompletionMajorBoxRanges RationalHeight

theorem policy_piece_source_pointwise (k A : ℕ) (p : Policy) (s : Shape)
    (hk : 3≤k) (hA : 0<A) (hdim : p.phi.size+extra s+2=k)
    (hred : Reduction s k p.phi.size A) (D : ℝ) (hD : 1≤D)
    (hguard : PolicyAnalyticGuards k p) (coefficient : Curve)
    (hadm : AdmissibleCurve (2*k) coefficient)
    (halloc : ∀i : Fin p.pieces.size,PieceAllocationValid p.phi.size p.pieces[i.val]!)
    (hv : ∀i : Fin p.pieces.size,∀r,ResourcePhysicalShape k p (resourceAt p.pieces[i.val]! r))
    (hav : ∀i : Fin p.pieces.size,∀r,MomentAvailable coefficient (resourceAt p.pieces[i.val]! r).order)
    (top : ℝ) {rho ε : ℝ} (hrho : 0≤rho) (hε : 0<ε) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀α ell : ℝ,
      ell∈Set.Icc 0 top→
      P/R^rho≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
      P^ell≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→∀i : Fin p.pieces.size,
      ‖boxSourceFamily k (D*P) P R (fun i=>P^(phiReal p i)) α‖≤
        K*P^(amplitude k (phiReal p)+ε-min 1 (pieceSavingReal k p coefficient p.pieces[i.val]! ell)/root s) := by
  have hex := fun i : Fin p.pieces.size=>piece_source_pointwise k A p s hk hA hdim
    hred D hD hguard coefficient hadm p.pieces[i.val]! (halloc i) (hv i) (hav i) top hrho hε
  choose eta C T heta hC hT hb using hex
  let cut : Option (Fin p.pieces.size)→ℝ := fun i=>i.elim 1 eta
  let η : ℝ := Finset.univ.inf' Finset.univ_nonempty cut
  have hη : 0<η := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i hi
    cases i with
    | none=>norm_num [cut]
    | some i=>exact heta i
  have hηle (i : Fin p.pieces.size) : η≤eta i :=
    Finset.inf'_le cut (Finset.mem_univ (some i))
  let K : ℝ := 1+∑i,|C i|
  let P₀ : ℝ := 2+∑i,|T i|
  have hK : 0<K := by dsimp [K]; positivity
  have hP₀ : 2≤P₀ := by
    dsimp [P₀]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>abs_nonneg (T i)))
  have hCi (i : Fin p.pieces.size) : C i≤K := by
    have hh := Finset.single_le_sum (fun q _=>abs_nonneg (C q)) (Finset.mem_univ i)
    dsimp [K]
    linarith [le_abs_self (C i)]
  have hTi (i : Fin p.pieces.size) : T i≤P₀ := by
    have hh := Finset.single_le_sum (fun q _=>abs_nonneg (T q)) (Finset.mem_univ i)
    dsimp [P₀]
    linarith [le_abs_self (T i)]
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP R hR hRP α ell hell hm hh i
  have hP : 1≤P := by linarith [hP₀.trans hPP]
  exact (hb i P ((hTi i).trans hPP) R hR
    (hRP.trans (Real.rpow_le_rpow_of_exponent_le hP (hηle i))) α ell hell hm hh).trans
    (mul_le_mul_of_nonneg_right (hCi i) (Real.rpow_nonneg (zero_le_one.trans hP) _))

#print axioms policy_piece_source_pointwise
end Waring.PolicyCompletionPolicyPointwise
