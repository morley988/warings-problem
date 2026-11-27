import Waring.PolicyCompletionScaledShallowBox
import Waring.PolicyCompletionRefinedFactors

/-!
# Literal shallow resources on all three terminal Cartesian families

The complete shallow source estimate is transferred to the actual zero-,
first-, and second-difference factors. The phase multiplier and every
floor are literal. The source error cap is the only extra size condition.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledShallowFactors
open PolicyCompletionScaledShallowBox PolicyCompletionScaledBounds PolicyCompletionRefinedFactors PolicyCompletionQuadraticFactors
open CartesianMomentAdapters CartesianFloorScales CartesianResourceMoments
open FiniteResourceHolder ResourceDifferencingCap RationalHeight

theorem zeroFactors_shallow_on_floor_box {j k A : ℕ}
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (j+1)→ℝ) (he : ∀l,0<e l) (i : Fin (j+1))
    {T phi b rho ε : ℝ} (hk : 3≤k) (hA : 0<A)
    (hphi : 0<phi) (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-2-(k : ℝ)*T)
    (hcapPhi : b≤phi) (hcapError : b≤(k : ℝ)-5-(k : ℝ)*T+((k : ℝ)+2)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin (j+1)→Finset ℕ,
      (∀m∈C i,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→
      ∀V : Fin (j+1)→ℝ,P^phi≤V i→∀α t : ℝ,
      P/R^rho≤height (P^((k : ℝ)*(1-T))) α→
      average (fun x : realBox (scaledBounds Dscale P e) =>
        (zeroFactors (2*k) (A : ℝ) α (realCoefficientSets C) ⌊Dscale*P⌋₊ V t (some i) x.val)^2)
        ≤K*P^(ε-b) := by
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := coefficient_floor_box_shallow_physical
    hk (c := 4*A) (by omega) Dscale hDscale e he i hphi hb hrho hε hi htotal
    hcapPhi hcapError
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup C hC V hV α t hheight
  have hPp : 0<P := by have := hP₀.trans hPP₀; linarith
  have hb' := hbound P hPP₀ R hR hRup (C i) hC α hheight
  have hm := zero_coefficient_moment_eq (scaledBounds Dscale P e) ⌊Dscale*P⌋₊ (2*k) A 1 C V α t i
  simp only [Nat.mul_one] at hm
  rw [hm]
  exact (coefficientBoxMomentAt_mono_cap _ i (C i) (2*k) 1 _
    (Real.rpow_pos_of_pos hPp _) hV).trans hb'

theorem firstFactors_shallow_on_floor_box {j k A : ℕ}
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (j+1)→ℝ) (he : ∀l,0<e l) (i : Fin (j+1))
    {T phi b rho ε : ℝ} (hk : 3≤k) (hA : 0<A)
    (hphi : 0<phi) (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-3-(k : ℝ)*T)
    (hcapPhi : b≤phi) (hcapError : b≤(k : ℝ)-5-(k : ℝ)*T+((k : ℝ)+2)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin (j+1)→Finset ℕ,
      (∀m∈C i,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→
      ∀V : Fin (j+1)→ℝ,P^phi≤V i→∀α t : ℝ,
      P/R^rho≤height (P^((k : ℝ)*(1-T))) α→
      average (fun x : realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ) =>
        (firstFactors (2*k) (A : ℝ) α (realCoefficientSets C) ⌊Dscale*P⌋₊ V t (some i) x.val)^2)
        ≤K*P^(ε-b) := by
  let ex : Fin (j+2)→ℝ := Fin.cons 1 e
  have hex : ∀l,0<ex l := by
    intro l
    exact Fin.cases (by norm_num [ex]) (fun l=>he l) l
  have hex_i : ex i.succ=1-(k : ℝ)*phi := hi
  have hex_total : (∑l,ex l)=(k : ℝ)-2-(k : ℝ)*T := by
    simp only [ex,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,htotal]
    ring
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := coefficient_floor_box_shallow_physical
    hk (c := 4*A) (by omega) Dscale hDscale ex hex i.succ hphi hb hrho hε hex_i hex_total
    hcapPhi hcapError
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup C hC V hV α t hheight
  have hPp : 0<P := by have := hP₀.trans hPP₀; linarith
  have hb' := hbound P hPP₀ R hR hRup (C i) hC α hheight
  change coefficientBoxMomentAt (scaledBounds Dscale P (Fin.cons 1 e)) i.succ (C i)
    (2*k) 1 (P^phi) (((4*A : ℕ) : ℝ)*α)≤_ at hb'
  rw [scaled_bounds_cons_one] at hb'
  have hm := first_coefficient_moment_eq (scaledBounds Dscale P e) ⌊Dscale*P⌋₊ (2*k) A 1 C V α t i
  simp only [Nat.mul_one] at hm
  rw [hm]
  exact (coefficientBoxMomentAt_mono_cap _ i.succ (C i) (2*k) 1 _
    (Real.rpow_pos_of_pos hPp _) hV).trans hb'

theorem secondFactors_shallow_on_floor_box {j k A : ℕ}
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (j+1)→ℝ) (he : ∀l,0<e l) (i : Fin (j+1))
    {T phi b rho ε : ℝ} (hk : 3≤k) (hA : 0<A)
    (hphi : 0<phi) (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-4-(k : ℝ)*T)
    (hcapPhi : b≤phi) (hcapError : b≤(k : ℝ)-5-(k : ℝ)*T+((k : ℝ)+2)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin (j+1)→Finset ℕ,
      (∀m∈C i,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→
      ∀V : Fin (j+1)→ℝ,P^phi≤V i→∀α t : ℝ,
      P/R^rho≤height (P^((k : ℝ)*(1-T))) α→
      average (fun x : (realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)) ×ˢ
          Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ) =>
        (secondFactors (2*k) (A : ℝ) α (realCoefficientSets C) ⌊Dscale*P⌋₊ V t (some i) x.val)^2)
        ≤K*P^(ε-b) := by
  let ex : Fin (j+3)→ℝ := Fin.cons 1 (Fin.cons 1 e)
  have hex : ∀l,0<ex l := by
    intro l
    exact Fin.cases (by norm_num [ex])
      (fun l=>Fin.cases (by norm_num [ex]) (fun l=>he l) l) l
  have hex_i : ex i.succ.succ=1-(k : ℝ)*phi := hi
  have hex_total : (∑l,ex l)=(k : ℝ)-2-(k : ℝ)*T := by
    simp only [ex,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,htotal]
    ring
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := coefficient_floor_box_shallow_physical
    hk (c := 4*A) (by omega) Dscale hDscale ex hex i.succ.succ hphi hb hrho hε hex_i hex_total
    hcapPhi hcapError
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup C hC V hV α t hheight
  have hPp : 0<P := by have := hP₀.trans hPP₀; linarith
  have hb' := hbound P hPP₀ R hR hRup (C i) hC α hheight
  change coefficientBoxMomentAt (scaledBounds Dscale P (Fin.cons 1 (Fin.cons 1 e))) i.succ.succ (C i)
    (2*k) 1 (P^phi) (((4*A : ℕ) : ℝ)*α)≤_ at hb'
  rw [scaled_bounds_cons_one,scaled_bounds_cons_one] at hb'
  have hm := second_coefficient_moment_eq (scaledBounds Dscale P e) ⌊Dscale*P⌋₊ (2*k) A 1 C V α t i
  simp only [Nat.mul_one] at hm
  rw [hm]
  exact (coefficientBoxMomentAt_mono_cap _ i.succ.succ (C i) (2*k) 1 _
    (Real.rpow_pos_of_pos hPp _) hV).trans hb'

#print axioms zeroFactors_shallow_on_floor_box
#print axioms firstFactors_shallow_on_floor_box
#print axioms secondFactors_shallow_on_floor_box
end Waring.PolicyCompletionScaledShallowFactors
