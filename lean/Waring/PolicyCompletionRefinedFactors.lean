import Waring.PolicyCompletionRefinedBox
import Waring.PolicyCompletionQuadraticFactors

/-!
# Literal refined averages of the source coefficient factors

This identifies the actual first ordinary-difference coefficient resource
with the proved Cartesian floor-box average. The source normalization may
retain its extra smoothness factor: any V_i>=P^phi is allowed.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionRefinedFactors
open PolicyCompletionRefinedBox PolicyCompletionQuadraticFactors
open CartesianResourceMoments CartesianMomentAdapters CartesianFloorScales
open CartesianProductSampling FiniteResourceHolder NormalizedCoefficient
open ResourceDifferencingCap SmoothMoments RationalHeight

theorem coefficientBoxMomentAt_mono_cap {r : ℕ} (bounds : Fin (r+1) → ℕ)
    (i : Fin (r+1)) (C : Finset ℕ) (degree power : ℕ) (α : ℝ)
    {cap small : ℝ} (hsmall : 0 < small) (hcap : small ≤ cap) :
    coefficientBoxMomentAt bounds i C degree power cap α ≤
      coefficientBoxMomentAt bounds i C degree power small α := by
  unfold coefficientBoxMomentAt average
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro x hx
  apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (hsmall.le.trans hcap))
  exact div_le_div_of_nonneg_left (norm_nonneg _) hsmall hcap

/-- Refined coefficient resource on the literal first-difference family.
The source moment admissibility is the input already quantified by policy
soundness; no resource estimate or integer-scale comparison is assumed. -/
theorem firstFactors_refined_on_floor_box {j k power A : ℕ}
    (e : Fin (j+1) → ℝ) (he : ∀ l, 0 < e l) (i : Fin (j+1))
    {T phi Δ ε : ℝ} (hA : 0 < A) (hk : 0 < k) (hpower : 1 ≤ power)
    (hT : T ≤ 1) (hphi : 0 < phi) (hε : 0 < ε)
    (hi : e i=1-(k : ℝ)*phi)
    (htotal : (∑ l, e l)=(k : ℝ)-3-(k : ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0 ≤ ((2*power : ℕ) : ℝ)-((2*k : ℕ) : ℝ)+Δ) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ C : Fin (j+1) → Finset ℕ, C i ⊆ smoothNumbers (P^phi*R) R →
      ∀ V : Fin (j+1) → ℝ, P^phi ≤ V i →
      ∀ α ell t : ℝ, P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      average (fun x : realBox (floorBounds P e) ×ˢ Finset.Icc (1 : ℤ) (⌊P⌋₊ : ℤ) =>
        (firstFactors (2*k) (A : ℝ) α (realCoefficientSets C) ⌊P⌋₊ V t (some i) x.val)^(2*power)) ≤
        K*P^(ε-refinedSaving k T phi ell Δ) := by
  let ex : Fin (j+2) → ℝ := Fin.cons 1 e
  have hex : ∀ l, 0 < ex l := by
    intro l
    exact Fin.cases (by norm_num [ex]) (fun l => he l) l
  have hex_i : ex i.succ=1-(k : ℝ)*phi := hi
  have hex_total : (∑ l, ex l)=(k : ℝ)-2-(k : ℝ)*T := by
    simp only [ex,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,htotal]
    ring
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := coefficient_floor_box_refined
    ex hex i.succ (c := 4*A) (by omega) hk hpower hT hphi hε hex_i hex_total hadm hlam
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup C hC V hV α ell t hheight
  have hPp : 0 < P := by have := hP₀.trans hPP₀; linarith
  have hb := hbound P hPP₀ R hR hRup (C i) hC α ell hheight
  change coefficientBoxMomentAt (floorBounds P (Fin.cons 1 e)) i.succ (C i)
    (2*k) power (P^phi) (((4*A : ℕ) : ℝ)*α) ≤ _ at hb
  rw [floorBounds_cons_one] at hb
  rw [first_coefficient_moment_eq]
  exact (coefficientBoxMomentAt_mono_cap _ i.succ (C i) (2*k) power _
    (Real.rpow_pos_of_pos hPp _) hV).trans hb

/-- The source smooth block itself satisfies the refined theorem's support
condition, including its strict lower and smoothness cutoffs. -/
theorem firstFactors_refined_smooth_blocks {j k power A : ℕ}
    (phiTuple : Fin (j+1) → ℝ) (i : Fin (j+1)) {T Δ ε : ℝ}
    (hh : ∀ l : Fin (j+1), 0 < 1-(k : ℝ)*phiTuple l)
    (hA : 0 < A) (hk : 0 < k) (hpower : 1 ≤ power)
    (hT : T ≤ 1) (hphi : 0 < phiTuple i) (hε : 0 < ε)
    (htotal : Finset.sum Finset.univ (fun l : Fin (j+1) => (1 : ℝ)-(k : ℝ)*phiTuple l)=
      (k : ℝ)-3-(k : ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0 ≤ ((2*power : ℕ) : ℝ)-((2*k : ℕ) : ℝ)+Δ) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ α ell t : ℝ, P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      average (fun x : realBox (floorBounds P (fun l : Fin (j+1) => 1-(k : ℝ)*phiTuple l)) ×ˢ
          Finset.Icc (1 : ℤ) (⌊P⌋₊ : ℤ) =>
        (firstFactors (2*k) (A : ℝ) α
          (realCoefficientSets (fun l : Fin (j+1) => CoefficientPower.coefficientBlock P R (P^(phiTuple l))))
          ⌊P⌋₊ (fun l : Fin (j+1) => P^(phiTuple l)*R) t (some i) x.val)^(2*power)) ≤
        K*P^(ε-refinedSaving k T (phiTuple i) ell Δ) := by
  obtain ⟨η,K,P₀,hη,hK,hP₀,hbound⟩ := firstFactors_refined_on_floor_box
    (fun l : Fin (j+1) => 1-(k : ℝ)*phiTuple l) hh i hA hk hpower hT hphi hε rfl htotal hadm hlam
  refine ⟨η,K,P₀,hη,hK,hP₀,?_⟩
  intro P hPP₀ R hR hRup α ell t hheight
  exact hbound P hPP₀ R hR hRup
    (fun l : Fin (j+1) => CoefficientPower.coefficientBlock P R (P^(phiTuple l)))
    (CoefficientPower.coefficientBlock_subset _ _ _)
    (fun l : Fin (j+1) => P^(phiTuple l)*R)
    (le_mul_of_one_le_right (Real.rpow_nonneg (by have := hP₀.trans hPP₀; linarith) _) hR)
    α ell t hheight

#print axioms firstFactors_refined_on_floor_box
#print axioms firstFactors_refined_smooth_blocks
end Waring.PolicyCompletionRefinedFactors
