import Waring.PolicyCompletionScaledSource
import Waring.PolicyCompletionScaledBounds
import Waring.PolicyCompletionBasicBox
import Waring.PolicyCompletionRefinedBox

/-!
# Shallow resources on the literal Cartesian floor boxes

The actual shallow moment is transported through the proved product
multiplicity bound. The original minor-arc height and the source error
cap are retained; no coefficient estimate is assumed.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionScaledShallowBox
open RationalHeight PolicyCompletionScaledSource PolicyCompletionScaledBounds PolicyCompletionBasicRanges PolicyCompletionBasicBox
open PolicyCompletionRefinedBox CartesianProductSampling CartesianFloorScales
open CartesianResourceMoments ProductMultiplicity NormalizedCoefficient

theorem coefficient_floor_box_shallow {r k c : ℕ} (hk : 3≤k) (hc : 0<c)
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (r+1)→ℝ) (he : ∀i,0<e i) (i : Fin (r+1))
    {phi b ε : ℝ} (hphi : 0<phi) (hb : 0<b) (hε : 0<ε)
    (hcapPhi : b≤phi)
    (hcapError : 2*e i+((2*k-2 : ℕ) : ℝ)*phi+b≤∑l : Fin r,e (i.succAbove l)) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀α : ℝ,
      P^((k : ℝ)*b)≤height (P^(3*e i+(∑l : Fin r,e (i.succAbove l))+((2*k : ℕ) : ℝ)*phi)) α→
      coefficientBoxMomentAt (scaledBounds Dscale P e) i A (2*k) 1 (P^phi) ((c : ℝ)*α)≤K*P^(ε-b) := by
  let other : Fin r→ℝ := fun l=>e (i.succAbove l)
  have hother : ∀l,0<other l := fun l=>he (i.succAbove l)
  have hj : 0≤∑l,other l := Finset.sum_nonneg fun l _=>(hother l).le
  obtain ⟨η,C,P₁,hη,hC,hP₁,hsource⟩ := normalized_shallow_scaled_cutoffs hk hc
    (CH := Dscale) (CJ := Dscale^r) hDscale (one_le_pow₀ hDscale)
    (he i) hj hphi hb (half_pos hε) hcapPhi hcapError
  let B := (∑l,other l)+1
  have hB : 0≤B := by dsimp [B]; linarith
  obtain ⟨D,hD,hbox⟩ := coefficient_box_at_to_sample r hB (half_pos hε)
  let P₀ := max P₁ (max (coordinateThreshold e) (2*Dscale^r))
  refine ⟨η,D*(2 : ℝ)^(r+1)*C,P₀,hη,by positivity,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP₀ R hR hRup A hA α hheight
  have hP₁P : P₁≤P := (le_max_left _ _).trans hP₀
  have hPe : coordinateThreshold e≤P :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hP₀
  have hconstant : 2*Dscale^r≤P :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hP₀
  have hP2 : 2≤P := hP₁.trans hP₁P
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hpow := scaled_coordinate_powers Dscale hDscale e he hPe
  have hbpos := scaled_bounds_pos e hpow
  have hpowother : ∀l,2≤Dscale*P^(other l) := fun l=>hpow (i.succAbove l)
  let J := scaledCutoff Dscale P other
  have hprod : (∏l∈Finset.univ.erase i,scaledBounds Dscale P e l)=scaledVolume Dscale P other := by
    rw [product_erase_eq_succAbove _ hbpos i]
    rfl
  have hVJ : (∏l∈Finset.univ.erase i,scaledBounds Dscale P e l)≤J := by
    rw [hprod]
    exact scaled_volume_le_cutoff (zero_le_one.trans hDscale) other (fun l=>(hother l).le) hPp.le hpowother
  have hpad : (J : ℝ)≤(2 : ℝ)^(r+1)*((∏l∈Finset.univ.erase i,scaledBounds Dscale P e l : ℕ) : ℝ) := by
    rw [hprod]
    exact scaled_cutoff_le_volume hDscale other (fun l=>(hother l).le) hP1 hpowother
  have hJup : (J : ℝ)≤P^B :=
    scaled_cutoff_le_power hDscale other (fun l=>(hother l).le) hP1 hconstant
  have hs := hsource P hP₁P R hR hRup A hA α (fun _=>1) hheight
  change normalizedSampledCoefficient A (2*k) 1 P phi (scaledBounds Dscale P e i) J ((c : ℝ)*α) (fun _=>1)≤_ at hs
  have hb' := hbox P hP1 (scaledBounds Dscale P e) hbpos i J hVJ hJup
    ((2 : ℝ)^(r+1)) hpad A (2*k) 1 phi ((c : ℝ)*α)
  apply hb'.trans
  calc
    _ ≤ D*(2 : ℝ)^(r+1)*P^(ε/2)*(C*P^(ε/2-b)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (D*(2 : ℝ)^(r+1)*C)*P^(ε-b) := by
      have hp : P^(ε/2)*P^(ε/2-b)=P^(ε-b) := by rw [← Real.rpow_add hPp]; congr 1; ring
      calc
        _ = (D*(2 : ℝ)^(r+1)*C)*(P^(ε/2)*P^(ε/2-b)) := by ring
        _ = _ := by rw [hp]

/-- The shallow source cap, on the original common
minor-arc height P/R^rho, for the actual Cartesian coefficient average. -/
theorem coefficient_floor_box_shallow_physical {r k c : ℕ} (hk : 3≤k) (hc : 0<c)
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (r+1)→ℝ) (he : ∀l,0<e l) (i : Fin (r+1))
    {T phi b rho ε : ℝ} (hphi : 0<phi) (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-2-(k : ℝ)*T)
    (hcapPhi : b≤phi) (hcapError : b≤(k : ℝ)-5-(k : ℝ)*T+((k : ℝ)+2)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀α : ℝ,
      P/R^rho≤height (P^((k : ℝ)*(1-T))) α→
      coefficientBoxMomentAt (scaledBounds Dscale P e) i A (2*k) 1 (P^phi) ((c : ℝ)*α)≤K*P^(ε-b) := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hothers : (∑l : Fin r,e (i.succAbove l))=(k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi := by
    have hs := Fin.sum_univ_succAbove e i
    rw [htotal,hi] at hs
    linarith
  have hdegree : ((2*k : ℕ) : ℝ)=2*(k : ℝ) := by push_cast; rfl
  have hdegree' : ((2*k-2 : ℕ) : ℝ)=2*(k : ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2≤2*k)]
    push_cast
    rfl
  have hcap : 2*e i+((2*k-2 : ℕ) : ℝ)*phi+b≤∑l : Fin r,e (i.succAbove l) := by
    rw [hi,hothers,hdegree']
    nlinarith only [hcapError]
  obtain ⟨ηs,K,P₀,hηs,hK,hP₀,hbound⟩ := coefficient_floor_box_shallow hk hc Dscale hDscale e he i
    hphi hb hε hcapPhi hcap
  have hkb : (k : ℝ)*b<1 := by
    have hh : 0<1-(k : ℝ)*phi := hi ▸ he i
    have hle := mul_le_mul_of_nonneg_left hcapPhi hkR.le
    linarith
  let η := min ηs ((1-(k : ℝ)*b)/(rho+1))
  have hη : 0<η := lt_min hηs (div_pos (sub_pos.mpr hkb) (by positivity))
  have hηs' : η≤ηs := min_le_left _ _
  have hηrho : rho*η≤1-(k : ℝ)*b := by
    have hh := (le_div_iff₀ (show 0<rho+1 by positivity)).mp
      (min_le_right ηs ((1-(k : ℝ)*b)/(rho+1)))
    have hη0 := hη.le
    nlinarith only [hh,hη0]
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup A hA α hheight
  have hP1 : 1≤P := by have hh := hP₀.trans hPP₀; linarith
  have hRup' := hRup.trans (Real.rpow_le_rpow_of_exponent_le hP1 hηs')
  have hh := (minor_height_power_lower hP1 hR hRup hrho hηrho).trans hheight
  have hQ : 3*e i+(∑l : Fin r,e (i.succAbove l))+((2*k : ℕ) : ℝ)*phi=(k : ℝ)*(1-T) := by
    rw [hi,hothers,hdegree]
    ring
  exact hbound P hPP₀ R hR hRup' A hA α (by simpa only [hQ] using hh)

#print axioms coefficient_floor_box_shallow
#print axioms coefficient_floor_box_shallow_physical
end Waring.PolicyCompletionScaledShallowBox
