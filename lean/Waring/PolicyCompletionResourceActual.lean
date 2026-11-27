import Waring.CertificateAllocation
import Waring.PolicyCompletionCoefficientShape
import Waring.PolicyCompletionResourceFormula
import Waring.PolicyCompletionMajorPowerRanges
import Waring.PolicyCompletionAdmissibleLower
import Waring.EndgameCompletionPolicySemanticsLookups

/-! # Every literal certificate resource follows from actual source estimates -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionResourceActual
open Certificate PolicyCompletionTerminalShape PolicyCompletionCoefficientShape
open PolicyCompletionResourceFormula PolicyCompletionMajorPowerRanges
open CartesianMomentAdapters RationalHeight NormalizedCoefficient SmoothMoments

theorem physical_factor_le {k : ℕ} {p : Policy} {r : Resource}
    (h : ResourcePhysicalShape k p r) : r.factor≤p.phi.size := by
  cases hk : r.kind <;> simp only [ResourcePhysicalShape,hk] at h
  · omega
  · omega
  · omega
  · exact h.2.1
  · exact h.2.1
  · exact h.2.1

def coefficientSets {j : ℕ} (φ : Fin j→ℝ) (P R : ℝ) (i : Fin j) : Finset ℕ :=
  CoefficientPower.coefficientBlock P R (P^(φ i))
def coefficientCaps {j : ℕ} (φ : Fin j→ℝ) (P R : ℝ) (i : Fin j) : ℝ := P^(φ i)*R

def actualResourceMoment (k A : ℕ) (p : Policy) (s : Shape) (D P R α t : ℝ)
    (φ : Fin p.phi.size→ℝ) (r : Resource) (hf : r.factor≤p.phi.size) : ℝ :=
  literalMoment s (2*k) A D P (shiftExponents k φ)
    (coefficientSets φ P R) (coefficientCaps φ P R) α t
    (allocationFactor p.phi.size r.factor hf) r.order

theorem actual_resource_bound (k A : ℕ) (p : Policy) (s : Shape)
    (hk : 3≤k) (hA : 0<A) (hdim : p.phi.size+extra s+2=k)
    (D : ℝ) (hD : 1≤D) (φ : Fin p.phi.size→ℝ)
    (hφ : ∀i,0<φ i) (he : ∀i,0<shiftExponents k φ i)
    (hφeq : ∀i,φ i=(p.phi[i.val]!:ℝ))
    (hT : total φ=(sumQ p.phi:ℝ)) (hh : 1<(heightExponent k p:ℝ))
    (coefficient : Curve) (hadm : AdmissibleCurve (2*k) coefficient)
    (r : Resource) (hv : ResourcePhysicalShape k p r)
    (havailable : r.kind=.refined ∨ r.kind=.cube → MomentAvailable coefficient r.order)
    {rho ε : ℝ} (hrho : 0≤rho) (hε : 0<ε) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀α ell t : ℝ,
      P/R^rho≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
      P^ell≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
      actualResourceMoment k A p s D P R α t φ r (physical_factor_le hv)≤
        K*P^(ε-resourceReal k p coefficient r ell) := by
  have hsum : (∑i,shiftExponents k φ i)=(k:ℝ)-2-(extra s:ℝ)-(k:ℝ)*(sumQ p.phi:ℝ) := by
    rw [shiftExponents_sum,hT]
    have hd : (p.phi.size:ℝ)+(extra s:ℝ)+2=(k:ℝ) := by exact_mod_cast hdim
    linarith
  have hheight : (∑i,shiftExponents k φ i)+(extra s:ℝ)=(heightExponent k p:ℝ) := by
    rw [hsum]
    simp only [heightExponent,q,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    ring
  have hconductor : (∑i,shiftExponents k φ i)+(extra s:ℝ)+2=(k:ℝ)*(1-(sumQ p.phi:ℝ)) := by
    rw [hsum]
    ring
  have hTle : (sumQ p.phi:ℝ)≤1 := by
    have hq := length_pos (by omega : p.phi.size<k) φ (fun i=>(he i).le)
    rw [hT] at hq
    linarith
  have hsupport {P R : ℝ} (i : Fin p.phi.size) :
      coefficientSets φ P R i⊆smoothNumbers (P^(φ i)*R) R :=
    CoefficientPower.coefficientBlock_subset _ _ _
  have hwindow {P R : ℝ} (i : Fin p.phi.size) :
      ∀m∈coefficientSets φ P R i,P^(φ i)<(m:ℝ) ∧ (m:ℝ)≤P^(φ i)*R := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  have hcap {P R : ℝ} (hP : 0≤P) (hR : 1≤R) (i : Fin p.phi.size) :
      P^(φ i)≤coefficientCaps φ P R i :=
    le_mul_of_one_le_right (Real.rpow_nonneg hP _) hR
  cases hkind : r.kind with
  | z2 =>
    have hv' : r.factor=0 ∧ r.order=2 := by simpa only [ResourcePhysicalShape,hkind] using hv
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := literal_z2 s D hD (shiftExponents k φ) he
      (by rwa [hheight]) rho hrho A hA hε
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α ell t hm hheight'
    have hb' := hb P hPP R hR hRP α t (by rwa [hconductor]) (2*k)
      (coefficientSets φ P R) (coefficientCaps φ P R)
    simpa only [actualResourceMoment,hv'.1,hv'.2,allocationFactor,dif_pos rfl,resourceReal,hkind] using hb'
  | z4 =>
    have hv' : r.factor=0 ∧ r.order=4 := by simpa only [ResourcePhysicalShape,hkind] using hv
    obtain ⟨K,P₀,hK,hP₀,hb⟩ := literal_fourth s D hD (shiftExponents k φ) he A hA hε
    refine ⟨1,K,P₀,by norm_num,hK,hP₀,?_⟩
    intro P hPP R hR hRP α ell t hm hh'
    have hb' := (hb P hPP α ell t (by rwa [hconductor]) (2*k)
      (coefficientSets φ P R) (coefficientCaps φ P R)).1
    rw [hheight] at hb'
    simpa only [actualResourceMoment,hv'.1,hv'.2,allocationFactor,dif_pos rfl,resourceReal,hkind,
      NormalizedQuadratic.z4Saving] using hb'
  | z4Refined =>
    have hv' : r.factor=0 ∧ r.order=4 := by simpa only [ResourcePhysicalShape,hkind] using hv
    obtain ⟨K,P₀,hK,hP₀,hb⟩ := literal_fourth s D hD (shiftExponents k φ) he A hA hε
    refine ⟨1,K,P₀,by norm_num,hK,hP₀,?_⟩
    intro P hPP R hR hRP α ell t hm hh'
    have hb' := (hb P hPP α ell t (by rwa [hconductor]) (2*k)
      (coefficientSets φ P R) (coefficientCaps φ P R)).2
    rw [hheight] at hb'
    simpa only [actualResourceMoment,hv'.1,hv'.2,allocationFactor,dif_pos rfl,resourceReal,hkind,
      NormalizedQuadratic.z4RefinedSaving,min_comm] using hb'
  | basic =>
    have hv' : 0<r.factor ∧ r.factor≤p.phi.size ∧ r.order=2 ∧ BasicPhysicalCaps k p r := by
      simpa only [ResourcePhysicalShape,hkind] using hv
    let i : Fin p.phi.size := ⟨r.factor-1,by omega⟩
    have hfac : allocationFactor p.phi.size r.factor (physical_factor_le hv)=some i := by
      simp [allocationFactor,ne_of_gt hv'.1,i]
    have hphi : φ i=(p.phi[r.factor-1]!:ℝ) := hφeq i
    have hc := hv'.2.2.2
    unfold BasicPhysicalCaps at hc
    have hbpos : (0:ℝ)<(resourceSizeCap k p r:ℝ) := by exact_mod_cast hc.1
    have hbf : (resourceSizeCap k p r:ℝ)≤φ i := by rw [hphi]; exact_mod_cast hc.2.1
    have hex : ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
        ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
        ∀C : Fin p.phi.size→Finset ℕ,
        (∀m∈C i,P^(φ i)<(m:ℝ) ∧ (m:ℝ)≤P^(φ i)*R)→
        ∀V : Fin p.phi.size→ℝ,P^(φ i)≤V i→∀α t : ℝ,
        P/R^rho≤height (P^((k:ℝ)*(1-(sumQ p.phi:ℝ)))) α→
        literalMoment s (2*k) A D P (shiftExponents k φ) C V α t (some i) 2≤
          K*P^(ε-(resourceSizeCap k p r:ℝ)) := by
      rcases hc.2.2 with hc|hc
      · apply literal_deep s D hD (shiftExponents k φ) he i hk hA (hφ i) hbpos hrho hε rfl hsum hbf
        · rw [hphi]
          simpa only [q,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hc.1
        · exact_mod_cast hc.2.1
        · rw [hphi]
          simpa only [q,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K:=ℝ)).mpr hc.2.2
      · apply literal_shallow s D hD (shiftExponents k φ) he i hk hA (hφ i) hbpos hrho hε rfl hsum hbf
        rw [hphi]
        simpa only [q,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hc
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := hex
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α ell t hm hh'
    have hb' := hb P hPP R hR hRP (coefficientSets φ P R) (hwindow i)
      (coefficientCaps φ P R) (hcap (by linarith [hP₀.trans hPP]) hR i) α t hm
    simpa only [actualResourceMoment,hfac,hv'.2.2.1,resourceReal,hkind] using hb'
  | refined =>
    have hv' : 0<r.factor ∧ r.factor≤p.phi.size ∧ 2≤r.order ∧ r.order%2=0 := by
      simpa only [ResourcePhysicalShape,hkind] using hv
    let i : Fin p.phi.size := ⟨r.factor-1,by omega⟩
    have hfac : allocationFactor p.phi.size r.factor (physical_factor_le hv)=some i := by
      simp [allocationFactor,ne_of_gt hv'.1,i]
    have hphi : φ i=(p.phi[r.factor-1]!:ℝ) := hφeq i
    have horder : r.order=2*(r.order/2) := by omega
    have hp : 1≤r.order/2 := by omega
    have ha : AdmissibleExcess (2*k) (2*(r.order/2))
        ((delta (2*k) coefficient r.order).getD 0:ℝ) := by
      rw [←horder]
      exact delta_getD_admissible hadm (havailable (Or.inl hkind))
    have hlam := admissibleExponent_even_ge_one hp ha
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := literal_refined s D hD (shiftExponents k φ) he i
      (by omega : 0<k) hA hp hTle (hφ i) hε rfl hsum ha (by linarith)
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α ell t hm hh'
    have hb' := hb P hPP R hR hRP (coefficientSets φ P R) (hsupport i)
      (coefficientCaps φ P R) (hcap (by linarith [hP₀.trans hPP]) hR i) α ell t hh'
    rw [resourceReal_refined k p coefficient r hkind,←hphi]
    rw [←horder] at hb'
    simpa only [actualResourceMoment,hfac] using hb'
  | cube =>
    have hv' : 0<r.factor ∧ r.factor≤p.phi.size ∧ 2≤r.order ∧ r.order%2=0 ∧ p.phi.size=k-2 := by
      simpa only [ResourcePhysicalShape,hkind] using hv
    have hs : s=.zero := by cases s <;> norm_num [extra] at hdim ⊢ <;> omega
    subst s
    let i : Fin p.phi.size := ⟨r.factor-1,by omega⟩
    have hfac : allocationFactor p.phi.size r.factor (physical_factor_le hv)=some i := by
      simp [allocationFactor,ne_of_gt hv'.1,i]
    have hphi : φ i=(p.phi[r.factor-1]!:ℝ) := hφeq i
    have horder : r.order=2*(r.order/2) := by omega
    have hp : 1≤r.order/2 := by omega
    have ha : AdmissibleExcess (2*k) (2*(r.order/2))
        ((delta (2*k) coefficient r.order).getD 0:ℝ) := by
      rw [←horder]
      exact delta_getD_admissible hadm (havailable (Or.inr hkind))
    have hlam := admissibleExponent_even_ge_one hp ha
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := literal_cube D hD (shiftExponents k φ) he i
      (by omega : 0<k) hA hp hTle (hφ i) hε rfl
      (by simpa only [extra,Nat.cast_zero,sub_zero] using hsum) ha (by linarith)
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α ell t hm hh'
    have hb' := hb P hPP R hR hRP (coefficientSets φ P R) (hsupport i)
      (coefficientCaps φ P R) (hcap (by linarith [hP₀.trans hPP]) hR i) α ell t hh'
    rw [resourceReal_cube k p coefficient r hkind,←hphi]
    rw [←horder] at hb'
    simpa only [actualResourceMoment,hfac] using hb'

#print axioms actual_resource_bound
end Waring.PolicyCompletionResourceActual
