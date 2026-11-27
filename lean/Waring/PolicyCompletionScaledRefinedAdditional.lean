import Waring.PolicyCompletionScaledRefinedBox
import Waring.PolicyCompletionScaledRefinedFactors

/-!
# Refined resources at quadratic and quartic terminals

These are the two remaining literal terminal shapes. The genuine smooth
coefficient admissibility is the only source input; all floor-box transport
and the exact phase multiplier are proved.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledRefinedAdditional
open PolicyCompletionScaledRefinedBox PolicyCompletionScaledRefinedFactors PolicyCompletionQuadraticFactors
open PolicyCompletionScaledBounds
open CartesianMomentAdapters CartesianFloorScales CartesianResourceMoments
open FiniteResourceHolder ResourceDifferencingCap RationalHeight NormalizedCoefficient SmoothMoments

theorem zeroFactors_refined_on_floor_box {j k power A : ℕ}
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (j+1)→ℝ) (he : ∀l,0<e l) (i : Fin (j+1))
    {T phi Δ ε : ℝ} (hk : 0<k) (hA : 0<A) (hpower : 1≤power)
    (hT : T≤1) (hphi : 0<phi) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-2-(k : ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0≤((2*power : ℕ) : ℝ)-((2*k : ℕ) : ℝ)+Δ) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin (j+1)→Finset ℕ,
      C i⊆smoothNumbers (P^phi*R) R→
      ∀V : Fin (j+1)→ℝ,P^phi≤V i→∀α ell t : ℝ,
      P^ell≤height (P^((k : ℝ)*(1-T))) α→
      average (fun x : realBox (scaledBounds Dscale P e) =>
        (zeroFactors (2*k) (A : ℝ) α (realCoefficientSets C) ⌊Dscale*P⌋₊ V t (some i) x.val)^(2*power))
        ≤K*P^(ε-refinedSaving k T phi ell Δ) := by
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := coefficient_floor_box_refined
    Dscale hDscale e he i (c := 4*A) (by omega) hk hpower hT hphi hε hi htotal hadm hlam
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup C hC V hV α ell t hheight
  have hPp : 0<P := by have := hP₀.trans hPP₀; linarith
  have hb' := hbound P hPP₀ R hR hRup (C i) hC α ell hheight
  have hm := zero_coefficient_moment_eq (scaledBounds Dscale P e) ⌊Dscale*P⌋₊ (2*k) A power C V α t i
  rw [hm]
  exact (coefficientBoxMomentAt_mono_cap _ i (C i) (2*k) power _
    (Real.rpow_pos_of_pos hPp _) hV).trans hb'

theorem secondFactors_refined_on_floor_box {j k power A : ℕ}
    (Dscale : ℝ) (hDscale : 1≤Dscale)
    (e : Fin (j+1)→ℝ) (he : ∀l,0<e l) (i : Fin (j+1))
    {T phi Δ ε : ℝ} (hk : 0<k) (hA : 0<A) (hpower : 1≤power)
    (hT : T≤1) (hphi : 0<phi) (hε : 0<ε)
    (hi : e i=1-(k : ℝ)*phi) (htotal : (∑l,e l)=(k : ℝ)-4-(k : ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0≤((2*power : ℕ) : ℝ)-((2*k : ℕ) : ℝ)+Δ) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin (j+1)→Finset ℕ,
      C i⊆smoothNumbers (P^phi*R) R→
      ∀V : Fin (j+1)→ℝ,P^phi≤V i→∀α ell t : ℝ,
      P^ell≤height (P^((k : ℝ)*(1-T))) α→
      average (fun x : (realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)) ×ˢ
          Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ) =>
        (secondFactors (2*k) (A : ℝ) α (realCoefficientSets C) ⌊Dscale*P⌋₊ V t (some i) x.val)^(2*power))
        ≤K*P^(ε-refinedSaving k T phi ell Δ) := by
  let ex : Fin (j+3)→ℝ := Fin.cons 1 (Fin.cons 1 e)
  have hex : ∀l,0<ex l := by
    intro l
    exact Fin.cases (by norm_num [ex])
      (fun l=>Fin.cases (by norm_num [ex]) (fun l=>he l) l) l
  have hex_i : ex i.succ.succ=1-(k : ℝ)*phi := hi
  have hex_total : (∑l,ex l)=(k : ℝ)-2-(k : ℝ)*T := by
    simp only [ex,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,htotal]
    ring
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := coefficient_floor_box_refined
    Dscale hDscale ex hex i.succ.succ (c := 4*A) (by omega) hk hpower hT hphi hε hex_i hex_total hadm hlam
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup C hC V hV α ell t hheight
  have hPp : 0<P := by have := hP₀.trans hPP₀; linarith
  have hb' := hbound P hPP₀ R hR hRup (C i) hC α ell hheight
  change coefficientBoxMomentAt (scaledBounds Dscale P (Fin.cons 1 (Fin.cons 1 e))) i.succ.succ (C i)
    (2*k) power (P^phi) (((4*A : ℕ) : ℝ)*α)≤_ at hb'
  rw [scaled_bounds_cons_one,scaled_bounds_cons_one] at hb'
  have hm := second_coefficient_moment_eq (scaledBounds Dscale P e) ⌊Dscale*P⌋₊ (2*k) A power C V α t i
  rw [hm]
  exact (coefficientBoxMomentAt_mono_cap _ i.succ.succ (C i) (2*k) power _
    (Real.rpow_pos_of_pos hPp _) hV).trans hb'

#print axioms zeroFactors_refined_on_floor_box
#print axioms secondFactors_refined_on_floor_box
end Waring.PolicyCompletionScaledRefinedAdditional
