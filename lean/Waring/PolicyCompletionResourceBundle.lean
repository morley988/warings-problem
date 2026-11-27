import Waring.PolicyCompletionResourceActual
import Waring.EndgameCompletionPolicySemanticsParameters

/-! # Simultaneous actual resource bounds for each finite certificate piece -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionResourceBundle
open Certificate PolicyCompletionTerminalShape PolicyCompletionResourceActual
open PolicyCompletionResourceFormula PolicyCompletionMajorPowerRanges RationalHeight

/-- All resource constants and the common smoothness cutoff are chosen before
P, R, the phase, the height, and the completion variable. -/
theorem piece_resource_bounds (k A : ℕ) (p : Policy) (s : Shape)
    (hk : 3≤k) (hA : 0<A) (hdim : p.phi.size+extra s+2=k)
    (D : ℝ) (hD : 1≤D) (hguard : PolicyAnalyticGuards k p)
    (coefficient : Curve) (hadm : AdmissibleCurve (2*k) coefficient)
    (piece : Piece) (hv : ∀r,ResourcePhysicalShape k p (resourceAt piece r))
    (hav : ∀r,MomentAvailable coefficient (resourceAt piece r).order)
    {rho ε : ℝ} (hrho : 0≤rho) (hε : 0<ε) :
    ∃η : ℝ,0<η ∧ ∃K : Fin piece.resources.size→ℝ,(∀r,0<K r) ∧
      ∃P₀ : ℝ,2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀α ell t : ℝ,
      P/R^rho≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
      P^ell≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→∀r,
      actualResourceMoment k A p s D P R α t (phiReal p) (resourceAt piece r)
        (physical_factor_le (hv r))≤K r*P^(ε-resourceReal k p coefficient (resourceAt piece r) ell) := by
  have hex := fun r => actual_resource_bound k A p s hk hA hdim D hD (phiReal p)
    (phiReal_pos hguard) (phiReal_shift_pos (by omega) hguard) (fun _=>rfl)
    (sumQ_cast_eq_total p).symm (by exact_mod_cast hguard.1)
    coefficient hadm (resourceAt piece r) (hv r) (fun _=>hav r) hrho hε
  choose eta K P₀ heta hK hP₀ hb using hex
  let cut : Option (Fin piece.resources.size)→ℝ := fun r=>r.elim 1 eta
  let η : ℝ := Finset.univ.inf' Finset.univ_nonempty cut
  have hη : 0<η := by
    apply (Finset.lt_inf'_iff _).mpr
    intro r hr
    cases r with
    | none=>norm_num [cut]
    | some r=>exact heta r
  have hηle (r : Fin piece.resources.size) : η≤eta r :=
    Finset.inf'_le cut (Finset.mem_univ (some r))
  let threshold : ℝ := 2+∑r,|P₀ r|
  have hthreshold : 2≤threshold := by
    dsimp [threshold]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun r _=>abs_nonneg (P₀ r)))
  have hthreshold_le (r : Fin piece.resources.size) : P₀ r≤threshold := by
    have hs : |P₀ r|≤∑q,|P₀ q| := Finset.single_le_sum (fun q _=>abs_nonneg (P₀ q)) (Finset.mem_univ r)
    dsimp [threshold]
    linarith [le_abs_self (P₀ r)]
  refine ⟨η,hη,K,hK,threshold,hthreshold,?_⟩
  intro P hPP R hR hRP α ell t hm hheight r
  have hP : 1≤P := by linarith [hthreshold.trans hPP]
  exact hb r P ((hthreshold_le r).trans hPP) R hR
    (hRP.trans (Real.rpow_le_rpow_of_exponent_le hP (hηle r))) α ell t hm hheight

#print axioms piece_resource_bounds
end Waring.PolicyCompletionResourceBundle
