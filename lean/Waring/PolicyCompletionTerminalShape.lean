import Waring.PolicyCompletionScaledRefinedAdditional
import Waring.PolicyCompletionScaledCubeFactors
import Waring.PolicyCompletionScaledBasicFactors
import Waring.PolicyCompletionScaledShallowFactors
import Waring.PolicyCompletionScaledFourthFactors

/-! # One literal interface for the three source terminal shapes -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionTerminalShape
open CartesianMomentAdapters CartesianFloorScales PolicyCompletionScaledBounds
open FiniteResourceHolder ResourceDifferencingCap RationalHeight NormalizedCoefficient SmoothMoments

inductive Shape where
  | zero | first | second
  deriving DecidableEq, Repr

def extra : Shape→ℕ
  | .zero=>0 | .first=>1 | .second=>2

def root : Shape→ℝ
  | .zero=>1 | .first=>2 | .second=>4

def Sample (j : ℕ) : Shape→Type
  | .zero => Fin j→ℝ
  | .first => (Fin j→ℝ)×ℤ
  | .second => ((Fin j→ℝ)×ℤ)×ℤ

def samples {j : ℕ} (s : Shape) (H : Finset (Fin j→ℝ)) (N : ℕ) : Finset (Sample j s) :=
  match s with
  | .zero=>H
  | .first=>H×ˢFinset.Icc (1:ℤ) (N:ℤ)
  | .second=>(H×ˢFinset.Icc (1:ℤ) (N:ℤ))×ˢFinset.Icc (1:ℤ) (N:ℤ)

def factors {j : ℕ} (s : Shape) (p : ℕ) (A α : ℝ) (C : Fin j→Finset ℝ)
    (N : ℕ) (V : Fin j→ℝ) (t : ℝ) : Option (Fin j)→Sample j s→ℝ :=
  match s with
  | .zero=>zeroFactors p A α C N V t
  | .first=>firstFactors p A α C N V t
  | .second=>secondFactors p A α C N V t

def literalMoment {j : ℕ} (s : Shape) (p A : ℕ) (D P : ℝ) (e : Fin j→ℝ)
    (C : Fin j→Finset ℕ) (V : Fin j→ℝ) (α t : ℝ) (i : Option (Fin j)) (order : ℕ) : ℝ :=
  average (fun x : samples s (realBox (scaledBounds D P e)) ⌊D*P⌋₊ =>
    (factors s p (A:ℝ) α (realCoefficientSets C) ⌊D*P⌋₊ V t i x.val)^order)

theorem literal_z2 {j : ℕ} (s : Shape) (D : ℝ) (hD : 1≤D)
    (e : Fin j→ℝ) (he : ∀i,0<e i) (hsum : 1<(∑i,e i)+(extra s:ℝ))
    (rho : ℝ) (hrho : 0≤rho) (A : ℕ) (hA : 0<A) {ε : ℝ} (hε : 0<ε) :
    ∃η K P₀ : ℝ,0<η ∧ 0<K ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀α t : ℝ,
      P/R^rho≤height (P^((∑i,e i)+(extra s:ℝ)+2)) α→
      ∀(p : ℕ)(C : Fin j→Finset ℕ)(V : Fin j→ℝ),
      literalMoment s p A D P e C V α t none 2≤K*P^(ε-1) := by
  cases s with
  | zero =>
    have hs : 1<∑i,e i := by simpa only [extra,Nat.cast_zero,add_zero] using hsum
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledQuadraticFactors.zeroFactors_z2_on_floor_box
      D hD e he hs rho hrho A hA hε
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α t hh p C V
    exact hb P hPP R hR hRP α t (by norm_num [extra,add_assoc] at hh ⊢; exact hh) p (realCoefficientSets C) V
  | first =>
    have hs : 0<∑i,e i := by norm_num [extra] at hsum; linarith
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledQuadraticFactors.firstFactors_z2_on_floor_box
      D hD e he hs rho hrho A hA hε
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α t hh p C V
    exact hb P hPP R hR hRP α t (by norm_num [extra,add_assoc] at hh ⊢; exact hh) p (realCoefficientSets C) V
  | second =>
    obtain ⟨η,K,P₀,hη,hK,hP₀,hb⟩ := PolicyCompletionScaledQuadraticFactors.secondFactors_z2_on_floor_box
      D hD e he rho hrho A hA hε
    refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
    intro P hPP R hR hRP α t hh p C V
    exact hb P hPP R hR hRP α t (by norm_num [extra,add_assoc] at hh ⊢; exact hh) p (realCoefficientSets C) V

theorem literal_fourth {j : ℕ} (s : Shape) (D : ℝ) (hD : 1≤D)
    (e : Fin j→ℝ) (he : ∀i,0<e i) (A : ℕ) (hA : 0<A) {ε : ℝ} (hε : 0<ε) :
    ∃K P₀ : ℝ,0<K ∧ 2≤P₀ ∧ ∀P : ℝ,P₀≤P→∀α ell t : ℝ,
      P^ell≤height (P^((∑i,e i)+(extra s:ℝ)+2)) α→
      ∀(p : ℕ)(C : Fin j→Finset ℕ)(V : Fin j→ℝ),
      literalMoment s p A D P e C V α t none 4≤K*P^(ε-NormalizedQuadratic.z4Saving ell ((∑i,e i)+(extra s:ℝ))) ∧
      literalMoment s p A D P e C V α t none 4≤K*P^(ε-NormalizedQuadratic.z4RefinedSaving ell ((∑i,e i)+(extra s:ℝ))) := by
  cases s with
  | zero =>
    obtain ⟨K,P₀,hK,hP₀,hb⟩ := PolicyCompletionScaledFourthFactors.zeroFactors_fourth_on_floor_box D hD e he A hA hε
    refine ⟨K,P₀,hK,hP₀,?_⟩
    intro P hPP α ell t hh p C V
    simpa only [literalMoment,samples,factors,extra,Nat.cast_zero,add_zero] using
      hb P hPP α ell t (by norm_num [extra,add_assoc] at hh ⊢; exact hh) p (realCoefficientSets C) V
  | first =>
    obtain ⟨K,P₀,hK,hP₀,hb⟩ := PolicyCompletionScaledFourthFactors.firstFactors_fourth_on_floor_box D hD e he A hA hε
    refine ⟨K,P₀,hK,hP₀,?_⟩
    intro P hPP α ell t hh p C V
    simpa only [literalMoment,samples,factors,extra,Nat.cast_one,Nat.cast_ofNat] using
      hb P hPP α ell t (by norm_num [extra,add_assoc] at hh ⊢; exact hh) p (realCoefficientSets C) V
  | second =>
    obtain ⟨K,P₀,hK,hP₀,hb⟩ := PolicyCompletionScaledFourthFactors.secondFactors_fourth_on_floor_box D hD e he A hA hε
    refine ⟨K,P₀,hK,hP₀,?_⟩
    intro P hPP α ell t hh p C V
    simpa only [literalMoment,samples,factors,extra,Nat.cast_one,Nat.cast_ofNat] using
      hb P hPP α ell t (by norm_num [extra,add_assoc] at hh ⊢; exact hh) p (realCoefficientSets C) V

#print axioms literal_z2
#print axioms literal_fourth
end Waring.PolicyCompletionTerminalShape
