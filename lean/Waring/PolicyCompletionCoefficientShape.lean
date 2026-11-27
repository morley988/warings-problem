import Waring.PolicyCompletionTerminalShape

/-! # The proved coefficient resources on each literal terminal domain -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionCoefficientShape
open PolicyCompletionTerminalShape
open CartesianMomentAdapters RationalHeight NormalizedCoefficient SmoothMoments

theorem literal_refined {j k power A : ℕ} (s : Shape)
    (D : ℝ) (hD : 1≤D) (e : Fin j→ℝ) (he : ∀i,0<e i) (i : Fin j)
    {T phi Δ ε : ℝ} (hk : 0<k) (hA : 0<A) (hpower : 1≤power)
    (hT : T≤1) (hphi : 0<phi) (hε : 0<ε) (hi : e i=1-(k:ℝ)*phi)
    (htotal : (∑l,e l)=(k:ℝ)-2-(extra s:ℝ)-(k:ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0≤((2*power:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin j→Finset ℕ,C i⊆smoothNumbers (P^phi*R) R→
      ∀V : Fin j→ℝ,P^phi≤V i→∀α ell t : ℝ,
      P^ell≤height (P^((k:ℝ)*(1-T))) α→
      literalMoment s (2*k) A D P e C V α t (some i) (2*power)≤
        K*P^(ε-refinedSaving k T phi ell Δ) := by
  cases j with
  | zero => exact Fin.elim0 i
  | succ j =>
    cases s with
    | zero =>
      have ht : (∑l,e l)=(k:ℝ)-2-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledRefinedAdditional.zeroFactors_refined_on_floor_box
        D hD e he i hk hA hpower hT hphi hε hi ht hadm hlam
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α ell t hh
      exact hb P hPP R hR hRP C hC V hV α ell t hh
    | first =>
      have ht : (∑l,e l)=(k:ℝ)-3-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledRefinedFactors.firstFactors_refined_on_floor_box
        D hD e he i hA hk hpower hT hphi hε hi ht hadm hlam
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α ell t hh
      exact hb P hPP R hR hRP C hC V hV α ell t hh
    | second =>
      have ht : (∑l,e l)=(k:ℝ)-4-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledRefinedAdditional.secondFactors_refined_on_floor_box
        D hD e he i hk hA hpower hT hphi hε hi ht hadm hlam
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α ell t hh
      exact hb P hPP R hR hRP C hC V hV α ell t hh

theorem literal_deep {j k A : ℕ} (s : Shape)
    (D : ℝ) (hD : 1≤D) (e : Fin j→ℝ) (he : ∀i,0<e i) (i : Fin j)
    {T phi b rho ε : ℝ} (hk : 3≤k) (hA : 0<A) (hphi : 0<phi)
    (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε) (hi : e i=1-(k:ℝ)*phi)
    (htotal : (∑l,e l)=(k:ℝ)-2-(extra s:ℝ)-(k:ℝ)*T)
    (hcapPhi : b≤phi) (hcap : b≤(k:ℝ)-6-(k:ℝ)*T+4*(k:ℝ)*phi)
    (hpow : 4*b≤1-T) (hbin : 6*b≤(k:ℝ)*(1-T)-(4*(k:ℝ)-1)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin j→Finset ℕ,
      (∀m∈C i,P^phi<(m:ℝ) ∧ (m:ℝ)≤P^phi*R)→
      ∀V : Fin j→ℝ,P^phi≤V i→∀α t : ℝ,
      P/R^rho≤height (P^((k:ℝ)*(1-T))) α→
      literalMoment s (2*k) A D P e C V α t (some i) 2≤K*P^(ε-b) := by
  cases j with
  | zero => exact Fin.elim0 i
  | succ j =>
    cases s with
    | zero =>
      have ht : (∑l,e l)=(k:ℝ)-2-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := PolicyCompletionScaledBasicFactors.zeroFactors_basic_on_floor_box
        D hD e he i hk hA hphi hb hrho hε hi ht hcapPhi hcap hpow hbin
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α t hh
      exact hbound P hPP R hR hRP C hC V hV α t hh
    | first =>
      have ht : (∑l,e l)=(k:ℝ)-3-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := PolicyCompletionScaledBasicFactors.firstFactors_basic_on_floor_box
        D hD e he i hk hA hphi hb hrho hε hi ht hcapPhi hcap hpow hbin
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α t hh
      exact hbound P hPP R hR hRP C hC V hV α t hh
    | second =>
      have ht : (∑l,e l)=(k:ℝ)-4-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := PolicyCompletionScaledBasicFactors.secondFactors_basic_on_floor_box
        D hD e he i hk hA hphi hb hrho hε hi ht hcapPhi hcap hpow hbin
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α t hh
      exact hbound P hPP R hR hRP C hC V hV α t hh

theorem literal_shallow {j k A : ℕ} (s : Shape)
    (D : ℝ) (hD : 1≤D) (e : Fin j→ℝ) (he : ∀i,0<e i) (i : Fin j)
    {T phi b rho ε : ℝ} (hk : 3≤k) (hA : 0<A) (hphi : 0<phi)
    (hb : 0<b) (hrho : 0≤rho) (hε : 0<ε) (hi : e i=1-(k:ℝ)*phi)
    (htotal : (∑l,e l)=(k:ℝ)-2-(extra s:ℝ)-(k:ℝ)*T)
    (hcapPhi : b≤phi) (hcap : b≤(k:ℝ)-5-(k:ℝ)*T+((k:ℝ)+2)*phi) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin j→Finset ℕ,
      (∀m∈C i,P^phi<(m:ℝ) ∧ (m:ℝ)≤P^phi*R)→
      ∀V : Fin j→ℝ,P^phi≤V i→∀α t : ℝ,
      P/R^rho≤height (P^((k:ℝ)*(1-T))) α→
      literalMoment s (2*k) A D P e C V α t (some i) 2≤K*P^(ε-b) := by
  cases j with
  | zero => exact Fin.elim0 i
  | succ j =>
    cases s with
    | zero =>
      have ht : (∑l,e l)=(k:ℝ)-2-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := PolicyCompletionScaledShallowFactors.zeroFactors_shallow_on_floor_box
        D hD e he i hk hA hphi hb hrho hε hi ht hcapPhi hcap
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α t hh
      exact hbound P hPP R hR hRP C hC V hV α t hh
    | first =>
      have ht : (∑l,e l)=(k:ℝ)-3-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := PolicyCompletionScaledShallowFactors.firstFactors_shallow_on_floor_box
        D hD e he i hk hA hphi hb hrho hε hi ht hcapPhi hcap
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α t hh
      exact hbound P hPP R hR hRP C hC V hV α t hh
    | second =>
      have ht : (∑l,e l)=(k:ℝ)-4-(k:ℝ)*T := by
        norm_num [extra] at htotal
        linarith
      obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := PolicyCompletionScaledShallowFactors.secondFactors_shallow_on_floor_box
        D hD e he i hk hA hphi hb hrho hε hi ht hcapPhi hcap
      refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
      intro P hPP R hR hRP C hC V hV α t hh
      exact hbound P hPP R hR hRP C hC V hV α t hh


theorem literal_cube {j k power A : ℕ}
    (D : ℝ) (hD : 1≤D) (e : Fin j→ℝ) (he : ∀i,0<e i) (i : Fin j)
    {T phi Δ ε : ℝ} (hk : 0<k) (hA : 0<A) (hpower : 1≤power)
    (hT : T≤1) (hphi : 0<phi) (hε : 0<ε) (hi : e i=1-(k:ℝ)*phi)
    (htotal : (∑l,e l)=(k:ℝ)-2-(k:ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0≤((2*power:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→
      ∀C : Fin j→Finset ℕ,C i⊆smoothNumbers (P^phi*R) R→
      ∀V : Fin j→ℝ,P^phi≤V i→∀α ell t : ℝ,
      P^ell≤height (P^((k:ℝ)*(1-T))) α→
      literalMoment .zero (2*k) A D P e C V α t (some i) (2*power)≤
        K*P^(ε-cubeSaving k T phi ell Δ) := by
  cases j with
  | zero => exact Fin.elim0 i
  | succ j =>
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledCubeFactors.zeroFactors_cube_on_floor_box
      D hD e he i hk hA hpower hT hphi hε hi htotal hadm hlam
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP C hC V hV α ell t hh
    exact hb P hPP R hR hRP C hC V hV α ell t hh

#print axioms literal_refined
#print axioms literal_deep
#print axioms literal_shallow
#print axioms literal_cube
end Waring.PolicyCompletionCoefficientShape
