import Waring.PolicyCompletionResourceBundle
import Waring.PolicyCompletionResourceCompact
import Waring.PolicyCompletionParameterScale
import Waring.PolicyCompletionShapeCap
import Waring.PolicyCompletionCapScalar

/-! # Actual pointwise minor-terminal saving of a certificate piece -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionResourcePointwise
open Certificate PolicyCompletionTerminalShape PolicyCompletionResourceActual
open PolicyCompletionResourceBundle PolicyCompletionResourceCompact PolicyCompletionResourceFormula
open PolicyCompletionMajorPowerRanges PolicyCompletionMajorBoxRanges PolicyCompletionParameterScale
open PolicyCompletionAllocationScale PolicyCompletionShapeCap PolicyCompletionCapScalar
open PolicyCompletionSourceCartesian PolicyCompletionScaledBounds CartesianFloorScales
open CartesianMomentAdapters ResourceDifferencingCap FiniteResourceHolder RationalHeight

theorem piece_source_pointwise (k A : ℕ) (p : Policy) (s : Shape)
    (hk : 3≤k) (hA : 0<A) (hdim : p.phi.size+extra s+2=k)
    (hred : Reduction s k p.phi.size A) (D : ℝ) (hD : 1≤D)
    (hguard : PolicyAnalyticGuards k p) (coefficient : Curve)
    (hadm : AdmissibleCurve (2*k) coefficient) (piece : Piece)
    (halloc : PieceAllocationValid p.phi.size piece)
    (hv : ∀r,ResourcePhysicalShape k p (resourceAt piece r))
    (hav : ∀r,MomentAvailable coefficient (resourceAt piece r).order)
    (top : ℝ) {rho ε : ℝ} (hrho : 0≤rho) (hε : 0<ε) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀α ell : ℝ,
      ell∈Set.Icc 0 top→
      P/R^rho≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
      P^ell≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
      ‖boxSourceFamily k (D*P) P R (fun i=>P^(phiReal p i)) α‖≤
        K*P^(amplitude k (phiReal p)+ε-min 1 (pieceSavingReal k p coefficient piece ell)/root s) := by
  let δ : ℝ := min (ε/4) 1
  have hδ : 0<δ := lt_min (by positivity) zero_lt_one
  have hδ1 : δ≤1 := min_le_right _ _
  have hδε : δ≤ε/4 := min_le_left _ _
  obtain ⟨ηr,hηr,K,hK,P₁,hP₁,hresources⟩ := piece_resource_bounds k A p s hk hA hdim
    D hD hguard coefficient hadm piece hv hav hrho hδ
  obtain ⟨B,hB,hbound⟩ := resourceReal_uniform_bound k p coefficient (resourceAt piece) top
  obtain ⟨Clog,hClog,hlog⟩ := completionLoss_scaled hD hδ
  let L : ℝ := 2*D
  have hL : 1≤L := by dsimp [L]; linarith
  let J : ℝ := L^(B+1)
  have hJ : 1≤J := Real.one_le_rpow hL (by linarith)
  have hJp : 0<J := zero_lt_one.trans_le hJ
  let T : ℝ := ∏r,(K r)^((resourceAt piece r).weight:ℝ)
  have hTp : 0<T := Finset.prod_pos (fun r _=>Real.rpow_pos_of_pos (hK r) _)
  let E : ℝ := 5*Clog*T*J
  have hE : 0<E := by dsimp [E]; positivity
  let U : ℝ := D^(p.phi.size+1)
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hU : 0<U := by dsimp [U]; positivity
  let C : ℝ := (prefactorA s+prefactorB s*E)^(1/root s)*U*L^(B+2)
  have hC : 0<C := by
    have ha := prefactorA_nonneg s
    have hb := prefactorB_pos s
    dsimp [C]
    positivity
  let η : ℝ := min ηr (ε/(2*((p.phi.size:ℝ)+1)))
  have hη : 0<η := lt_min hηr (div_pos hε (by positivity))
  let P₀ : ℝ := max P₁ (max (coordinateThreshold (shiftExponents k (phiReal p))) (2*D))
  refine ⟨η,C,P₀,hη,hC,hP₁.trans (le_max_left _ _),?_⟩
  intro P hPP R hR hRP α ell hell hm hh
  have hP₁P : P₁≤P := (le_max_left _ _).trans hPP
  have hP2 : 2≤P := hP₁.trans hP₁P
  have hP : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hPe : coordinateThreshold (shiftExponents k (phiReal p))≤P :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hPP
  have hPD : 2*D≤P := ((le_max_right _ _).trans (le_max_right _ _)).trans hPP
  have hφ := phiReal_pos hguard
  have he := phiReal_shift_pos (by omega : 0<k) hguard
  let N : ℕ := ⌊D*P⌋₊
  let H := realBox (scaledBounds D P (shiftExponents k (phiReal p)))
  let CC := realCoefficientSets (coefficientSets (phiReal p) P R)
  let V := coefficientCaps (phiReal p) P R
  have hcut := fixed_dilation_cutoff hD hP2
  have hN : 0<N := hcut.1
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hPN : P≤L*(N:ℝ) := hcut.2.2.1
  have hNP : (N:ℝ)≤L*P := hcut.2.2.2
  have hH : H.Nonempty := realBox_nonempty_of_pos _
    (scaled_bounds_pos _ (scaled_coordinate_powers D hD _ he hPe))
  have hV : ∀i,0<V i := coefficientCaps_pos hPp (zero_lt_one.trans_le hR) (phiReal p)
  have hCC : ∀i,((CC i).card:ℝ)≤V i := coefficientSets_real_card hPp.le (zero_le_one.trans hR) (phiReal p)
  have hCC0 : ∀i,∀m∈CC i,m≠0 := coefficientSets_real_ne_zero P R (phiReal p)
  let RR := pieceAllocation k p coefficient piece ell halloc K (fun r=>(hK r).le)
  let SS := scaledConstants RR J (zero_le_one.trans hJ)
  have hsave : ∀r,|RR.saving r|≤B := fun r=>hbound r ell hell
  have hS : |SS.totalSaving|≤B := by
    rw [scaledConstants_saving]
    exact totalSaving_abs_le RR hB.le hsave
  have hconst : SS.totalConstant≤T*J := scaledConstants_totalConstant_le RR hJ
  have heff : SS.effectiveConstant N≤E*P^δ := by
    have hl := hlog P hP hPD N hN hcut.2.1
    have htc := SS.totalConstant_nonneg
    unfold Allocation.effectiveConstant
    calc
      _ ≤ 5*(Clog*P^δ)*(T*J) := by gcongr
      _ = _ := by dsimp [E]; ring
  have hresource : ∀t∈Set.Icc (0:ℝ) 1,∀r,
      average (fun x : samples s H N=>(factors s (2*k) A α CC N V t (SS.factor r) x.val)^(SS.order r))≤
        SS.constant r*(N:ℝ)^(δ-SS.saving r) := by
    intro t ht
    apply moments_at_comparable_cutoff RR
      (fun i (x : samples s H N)=>factors s (2*k) A α CC N V t i x.val)
      hPp hNp hL hB.le hPN hNP hδ.le hδ1 hsave
    intro r
    have hb := hresources P hP₁P R hR
      (hRP.trans (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))) α ell t hm hh r
    simpa only [RR,pieceAllocation,actualResourceMoment,literalMoment,Real.rpow_natCast,H,CC,N,V] using hb
  have hpoly := shape_cap_with_loss SS s k A hred α H hH CC N N hN le_rfl V hV hCC hCC0 hδ.le hresource
  have hRpow : R^p.phi.size≤P^(ε/2) := by
    have hηj : η*(p.phi.size:ℝ)≤ε/2 := by
      have hη' : η≤ε/(2*((p.phi.size:ℝ)+1)) := min_le_right _ _
      have hm' := (le_div_iff₀ (by positivity : (0:ℝ)<2*((p.phi.size:ℝ)+1))).mp hη'
      nlinarith
    calc
      _ ≤ (P^η)^p.phi.size := pow_le_pow_left₀ (zero_le_one.trans hR) hRP _
      _ = P^(η*(p.phi.size:ℝ)) := (Real.rpow_mul_natCast hPp.le η p.phi.size).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hηj
  have hparam : (N:ℝ)*parameterScale H V≤U*P^(amplitude k (phiReal p)+ε/2) := by
    have hb := source_parameter_scale k hDp.le hPp (zero_le_one.trans hR)
      (phiReal p) (fun i=>(hφ i).le) (fun i=>(he i).le)
    calc
      _ ≤ U*R^p.phi.size*P^(amplitude k (phiReal p)) := hb
      _ ≤ U*P^(ε/2)*P^(amplitude k (phiReal p)) := by gcongr
      _ = _ := by rw [mul_assoc,←Real.rpow_add hPp]; congr 2; ring
  have hcap : ‖boxSourceFamily k (D*P) P R (fun i=>P^(phiReal p i)) α‖≤
      (prefactorA s+prefactorB s*SS.effectiveConstant N)^(1/root s)*
      (U*P^(amplitude k (phiReal p)+ε/2))*(N:ℝ)^(δ/root s-min 1 SS.totalSaving/root s) := by
    rw [source_box_power_eq_cartesian k hPp D R α (phiReal p)]
    exact hpoly.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hparam (Real.rpow_nonneg
        (add_nonneg (prefactorA_nonneg s) (mul_nonneg (prefactorB_pos s).le
          (SS.effectiveConstant_nonneg N hN))) _)) (Real.rpow_nonneg hNp.le _))
  have hout := scalar_scaled_cap (prefactorA_nonneg s) (prefactorB_pos s).le
    (SS.effectiveConstant_nonneg N hN) hE.le hU.le hP hNp hL hPN hNP hB.le hS
    hδ.le hδ1 (root_ge_one s) heff hcap
  have hsaving : SS.totalSaving=pieceSavingReal k p coefficient piece ell := by
    rw [scaledConstants_saving,pieceAllocation_totalSaving]
  rw [hsaving] at hout
  apply hout.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hP
  have hdiv : 2*δ/root s≤2*δ := div_le_self (by positivity) (root_ge_one s)
  linarith

#print axioms piece_source_pointwise
end Waring.PolicyCompletionResourcePointwise
