import Waring.PolicyCompletionBasicSource
import Waring.PolicyCompletionRefinedBox

/-!
# Basic coefficient resources on the literal Cartesian floor boxes

The established product-multiplicity theorem transfers the proved sampled
basic estimate to the actual tuple average. The original minor-arc height
and all four static cap conditions are retained explicitly.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicBox
open RationalHeight PolicyCompletionBasicSource PolicyCompletionBasicRanges
open PolicyCompletionRefinedBox CartesianProductSampling CartesianFloorScales
open CartesianResourceMoments ProductMultiplicity NormalizedCoefficient

theorem coefficient_floor_box_basic {r d c : ℕ} (hd : 6≤d) (hc : 0<c)
    (e : Fin (r+1)→ℝ) (he : ∀i,0<e i) (i : Fin (r+1))
    {phi b ε : ℝ} (hphi : 0<phi) (hb : 0<b) (hε : 0<ε)
    (hcapPhi : b≤phi)
    (hcapCubic : 3*e i+b≤∑l : Fin r,e (i.succAbove l))
    (hcapPower : 2*(d : ℝ)*b≤3*e i+(∑l : Fin r,e (i.succAbove l))+(d : ℝ)*phi)
    (hcapBinomial : 6*b+((d-1 : ℕ) : ℝ)*phi≤3*e i+∑l : Fin r,e (i.succAbove l)) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀α : ℝ,
      P^((d : ℝ)*b/2)≤height (P^(3*e i+(∑l : Fin r,e (i.succAbove l))+(d : ℝ)*phi)) α→
      coefficientBoxMomentAt (floorBounds P e) i A d 1 (P^phi) ((c : ℝ)*α)≤K*P^(ε-b) := by
  let other : Fin r→ℝ := fun l=>e (i.succAbove l)
  have hother : ∀l,0<other l := fun l=>he (i.succAbove l)
  have hj : 0≤∑l,other l := Finset.sum_nonneg fun l _=>(hother l).le
  obtain ⟨η,C,P₁,hη,hC,hP₁,hsource⟩ := normalized_basic_floor_cutoffs hd hc
    (he i) hj hphi hb (half_pos hε) hcapPhi hcapCubic hcapPower hcapBinomial
  let B := (∑l,other l)+1
  have hB : 0≤B := by dsimp [B]; linarith
  obtain ⟨D,hD,hbox⟩ := coefficient_box_at_to_sample r hB (half_pos hε)
  let P₀ := max P₁ (coordinateThreshold e)
  refine ⟨η,D*(2 : ℝ)^(r+1)*C,P₀,hη,by positivity,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP₀ R hR hRup A hA α hheight
  have hP₁P : P₁≤P := (le_max_left _ _).trans hP₀
  have hPe : coordinateThreshold e≤P := (le_max_right _ _).trans hP₀
  have hP2 : 2≤P := hP₁.trans hP₁P
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hpow := coordinate_powers_ge_two e he hPe
  have hbpos := floorBounds_pos e hpow
  have hpowother : ∀l,2≤P^(other l) := fun l=>hpow (i.succAbove l)
  let J := paddedCutoff P other
  have hprod : (∏l∈Finset.univ.erase i,floorBounds P e l)=actualVolume P other := by
    rw [product_erase_eq_succAbove _ hbpos i]
    rfl
  have hVJ : (∏l∈Finset.univ.erase i,floorBounds P e l)≤J := by
    rw [hprod]
    exact actualVolume_le_paddedCutoff other (fun l=>(hother l).le) hPp.le hpowother
  have hpad : (J : ℝ)≤(2 : ℝ)^(r+1)*((∏l∈Finset.univ.erase i,floorBounds P e l : ℕ) : ℝ) := by
    rw [hprod]
    exact paddedCutoff_le_actualVolume other (fun l=>(hother l).le) hP1 hpowother
  have hJup : (J : ℝ)≤P^B := by
    calc
      _ ≤ 2*P^(∑l,other l) := paddedCutoff_le_twice_power other (fun l=>(hother l).le) hP1
      _ ≤ P*P^(∑l,other l) := mul_le_mul_of_nonneg_right hP2 (Real.rpow_nonneg hPp.le _)
      _ = P^B := by
        nth_rw 1 [← Real.rpow_one P]
        rw [← Real.rpow_add hPp]
        congr 1
        dsimp [B]
        ring
  have hs := hsource P hP₁P R hR hRup A hA α (fun _=>1) hheight
  change normalizedSampledCoefficient A d 1 P phi (floorBounds P e i) J ((c : ℝ)*α) (fun _=>1)≤_ at hs
  have hb' := hbox P hP1 (floorBounds P e) hbpos i J hVJ hJup
    ((2 : ℝ)^(r+1)) hpad A d 1 phi ((c : ℝ)*α)
  apply hb'.trans
  calc
    _ ≤ D*(2 : ℝ)^(r+1)*P^(ε/2)*(C*P^(ε/2-b)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (D*(2 : ℝ)^(r+1)*C)*P^(ε-b) := by
      have hp : P^(ε/2)*P^(ε/2-b)=P^(ε-b) := by rw [← Real.rpow_add hPp]; congr 1; ring
      calc
        _ = (D*(2 : ℝ)^(r+1)*C)*(P^(ε/2)*P^(ε/2-b)) := by ring
        _ = _ := by rw [hp]

theorem minor_height_power_lower {P R rho η ell : ℝ}
    (hP : 1≤P) (hR : 1≤R) (hRup : R≤P^η) (hrho : 0≤rho)
    (hη : rho*η≤1-ell) : P^ell≤P/R^rho := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hRpower : R^rho≤P^(1-ell) := by
    calc
      _ ≤ (P^η)^rho := Real.rpow_le_rpow hRp.le hRup hrho
      _ = P^(rho*η) := by rw [← Real.rpow_mul hPp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hη
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hRp _)).mpr
  calc
    _ ≤ P^ell*P^(1-ell) := mul_le_mul_of_nonneg_left hRpower (Real.rpow_nonneg hPp.le _)
    _ = P := by rw [← Real.rpow_add hPp]; convert Real.rpow_one P using 1 <;> congr 1 <;> ring

/-- The certificate's four static basic caps, on the original common
minor-arc height P/R^rho, for the actual Cartesian coefficient average. -/
theorem coefficient_floor_box_basic_physical {r k c : ℕ} (hk : 3≤k) (hc : 0<c)
    (e : Fin (r+1)→ℝ) (he : ∀l,0<e l) (i : Fin (r+1))
    {T phi b rho ε : ℝ} (hphi : 0<phi) (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-2-(k : ℝ)*T)
    (hcapPhi : b≤phi) (hcapCubic : b≤(k : ℝ)-6-(k : ℝ)*T+4*(k : ℝ)*phi)
    (hcapPower : 4*b≤1-T) (hcapBinomial : 6*b≤(k : ℝ)*(1-T)-(4*(k : ℝ)-1)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀α : ℝ,
      P/R^rho≤height (P^((k : ℝ)*(1-T))) α→
      coefficientBoxMomentAt (floorBounds P e) i A (2*k) 1 (P^phi) ((c : ℝ)*α)≤K*P^(ε-b) := by
  have hkR : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hothers : (∑l : Fin r,e (i.succAbove l))=(k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi := by
    have hs := Fin.sum_univ_succAbove e i
    rw [htotal,hi] at hs
    linarith
  have hdegree : ((2*k : ℕ) : ℝ)=2*(k : ℝ) := by push_cast; rfl
  have hdegree' : ((2*k-1 : ℕ) : ℝ)=2*(k : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤2*k)]
    push_cast
    rfl
  have hcap1 : 3*e i+b≤∑l : Fin r,e (i.succAbove l) := by rw [hi,hothers]; linarith
  have hcap2 : 2*((2*k : ℕ) : ℝ)*b≤3*e i+(∑l : Fin r,e (i.succAbove l))+((2*k : ℕ) : ℝ)*phi := by
    rw [hi,hothers,hdegree]
    have hh := mul_le_mul_of_nonneg_left hcapPower hkR.le
    nlinarith only [hh]
  have hcap3 : 6*b+((2*k-1 : ℕ) : ℝ)*phi≤3*e i+∑l : Fin r,e (i.succAbove l) := by
    rw [hi,hothers,hdegree']
    nlinarith only [hcapBinomial]
  obtain ⟨ηs,K,P₀,hηs,hK,hP₀,hbound⟩ := coefficient_floor_box_basic (by omega : 6≤2*k) hc e he i
    hphi hb hε hcapPhi hcap1 hcap2 hcap3
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
  have hL : ((2*k : ℕ) : ℝ)*b/2=(k : ℝ)*b := by rw [hdegree]; ring
  exact hbound P hPP₀ R hR hRup' A hA α (by simpa only [hQ,hL] using hh)

#print axioms coefficient_floor_box_basic
#print axioms coefficient_floor_box_basic_physical
end Waring.PolicyCompletionBasicBox
