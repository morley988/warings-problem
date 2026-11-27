import Waring.PolicyCompletionScaledFourthBox
import Waring.PolicyCompletionScaledQuadraticFactors

/-!
# Literal fourth resources for every terminal shape

Both z4 branches are proved for the original zero-, one-, and two-step
ordinary-difference factors, with their exact completion support and cap.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledFourthFactors
open PolicyCompletionScaledFourthBox PolicyCompletionQuadraticFactors
open PolicyCompletionScaledBounds PolicyCompletionScaledQuadraticFactors
open CartesianMomentAdapters CartesianFloorScales CartesianResourceMoments
open FiniteResourceHolder ResourceDifferencingCap RationalHeight NormalizedQuadratic
open CartesianPolynomialBounds

theorem zeroFactors_fourth_on_floor_box {j : ℕ} (Dscale : ℝ) (hDscale : 1≤Dscale) (e : Fin j→ℝ) (he : ∀i,0<e i)
    (A : ℕ) (hA : 0<A) {ε : ℝ} (hε : 0<ε) :
    ∃K P₀ : ℝ,0<K ∧ 2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀α ell t : ℝ,
      P^ell≤height (P^((∑i,e i)+2)) α→∀(p : ℕ)(C : Fin j→Finset ℝ)(V : Fin j→ℝ),
      average (fun x : realBox (scaledBounds Dscale P e)=>
        (zeroFactors p (A : ℝ) α C ⌊Dscale*P⌋₊ V t none x.val)^4)≤K*P^(ε-z4Saving ell (∑i,e i)) ∧
      average (fun x : realBox (scaledBounds Dscale P e)=>
        (zeroFactors p (A : ℝ) α C ⌊Dscale*P⌋₊ V t none x.val)^4)≤K*P^(ε-z4RefinedSaving ell (∑i,e i)) := by
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := quadratic_floor_box_fourth Dscale hDscale e he (3*A) (by omega) hε
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro P hPP₀ α ell t hheight p C V
  have hP2 := hP₀.trans hPP₀
  have hPp : 0<P := by linarith
  have hb := hbound P hPP₀ α ell t hheight
  rw [zero_quadratic_moment_eq]
  have hm := quadraticBoxMoment_mono_cap (scaledBounds Dscale P e) (centeredSet ⌊Dscale*P⌋₊) α t (3*A) 4 hPp
    (scaled_quadratic_cap hDscale hP2)
  exact ⟨hm.trans hb.1,hm.trans hb.2⟩

theorem firstFactors_fourth_on_floor_box {j : ℕ} (Dscale : ℝ) (hDscale : 1≤Dscale) (e : Fin j→ℝ) (he : ∀i,0<e i)
    (A : ℕ) (hA : 0<A) {ε : ℝ} (hε : 0<ε) :
    ∃K P₀ : ℝ,0<K ∧ 2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀α ell t : ℝ,
      P^ell≤height (P^((∑i,e i)+3)) α→∀(p : ℕ)(C : Fin j→Finset ℝ)(V : Fin j→ℝ),
      average (fun x : realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)=>
        (firstFactors p (A : ℝ) α C ⌊Dscale*P⌋₊ V t none x.val)^4)≤K*P^(ε-z4Saving ell ((∑i,e i)+1)) ∧
      average (fun x : realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)=>
        (firstFactors p (A : ℝ) α C ⌊Dscale*P⌋₊ V t none x.val)^4)≤K*P^(ε-z4RefinedSaving ell ((∑i,e i)+1)) := by
  let ex : Fin (j+1)→ℝ := Fin.cons 1 e
  have hex : ∀i,0<ex i := fun i=>Fin.cases (by norm_num [ex]) he i
  have hsum : (∑i,ex i)=(∑i,e i)+1 := by
    simp only [ex,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    ring
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := quadratic_floor_box_fourth Dscale hDscale ex hex (3*A) (by omega) hε
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro P hPP₀ α ell t hheight p C V
  have hP2 := hP₀.trans hPP₀
  have hPp : 0<P := by linarith
  have hb := hbound P hPP₀ α ell t (by
    rw [hsum,show (∑i,e i)+1+2=(∑i,e i)+3 by ring]
    exact hheight)
  rw [hsum] at hb
  change quadraticBoxMoment (scaledBounds Dscale P (Fin.cons 1 e)) _ _ _ _ _ _≤_ ∧ _ at hb
  rw [scaled_bounds_cons_one] at hb
  rw [first_quadratic_moment_eq]
  have hm := quadraticBoxMoment_mono_cap (Fin.cons ⌊Dscale*P⌋₊ (scaledBounds Dscale P e)) (centeredSet ⌊Dscale*P⌋₊) α t (3*A) 4 hPp
    (scaled_quadratic_cap hDscale hP2)
  exact ⟨hm.trans hb.1,hm.trans hb.2⟩

theorem secondFactors_fourth_on_floor_box {j : ℕ} (Dscale : ℝ) (hDscale : 1≤Dscale) (e : Fin j→ℝ) (he : ∀i,0<e i)
    (A : ℕ) (hA : 0<A) {ε : ℝ} (hε : 0<ε) :
    ∃K P₀ : ℝ,0<K ∧ 2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀α ell t : ℝ,
      P^ell≤height (P^((∑i,e i)+4)) α→∀(p : ℕ)(C : Fin j→Finset ℝ)(V : Fin j→ℝ),
      average (fun x : (realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)) ×ˢ
          Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)=>
        (secondFactors p (A : ℝ) α C ⌊Dscale*P⌋₊ V t none x.val)^4)≤K*P^(ε-z4Saving ell ((∑i,e i)+2)) ∧
      average (fun x : (realBox (scaledBounds Dscale P e) ×ˢ Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)) ×ˢ
          Finset.Icc (1 : ℤ) (⌊Dscale*P⌋₊ : ℤ)=>
        (secondFactors p (A : ℝ) α C ⌊Dscale*P⌋₊ V t none x.val)^4)≤K*P^(ε-z4RefinedSaving ell ((∑i,e i)+2)) := by
  let ex : Fin (j+2)→ℝ := Fin.cons 1 (Fin.cons 1 e)
  have hex : ∀i,0<ex i := fun i=>Fin.cases (by norm_num [ex])
    (fun i=>Fin.cases (by norm_num [ex]) he i) i
  have hsum : (∑i,ex i)=(∑i,e i)+2 := by
    simp only [ex,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    ring
  obtain ⟨K,P₀,hK,hP₀,hbound⟩ := quadratic_floor_box_fourth Dscale hDscale ex hex (3*A) (by omega) hε
  refine ⟨K,P₀,hK,hP₀,?_⟩
  intro P hPP₀ α ell t hheight p C V
  have hP2 := hP₀.trans hPP₀
  have hPp : 0<P := by linarith
  have hb := hbound P hPP₀ α ell t (by
    rw [hsum,show (∑i,e i)+2+2=(∑i,e i)+4 by ring]
    exact hheight)
  rw [hsum] at hb
  change quadraticBoxMoment (scaledBounds Dscale P (Fin.cons 1 (Fin.cons 1 e))) _ _ _ _ _ _≤_ ∧ _ at hb
  rw [scaled_bounds_cons_one,scaled_bounds_cons_one] at hb
  rw [second_quadratic_moment_eq]
  have hm := quadraticBoxMoment_mono_cap (Fin.cons ⌊Dscale*P⌋₊ (Fin.cons ⌊Dscale*P⌋₊ (scaledBounds Dscale P e))) (centeredSet ⌊Dscale*P⌋₊) α t (3*A) 4 hPp
    (scaled_quadratic_cap hDscale hP2)
  exact ⟨hm.trans hb.1,hm.trans hb.2⟩

#print axioms zeroFactors_fourth_on_floor_box
#print axioms firstFactors_fourth_on_floor_box
#print axioms secondFactors_fourth_on_floor_box
end Waring.PolicyCompletionScaledFourthFactors
