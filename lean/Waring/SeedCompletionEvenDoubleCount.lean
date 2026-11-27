import Waring.SeedCompletionEvenDouble
import Waring.SeedCompletionCurveFamilies
import Waring.SeedCompletionProductGrouping

/-! # Genuine even j=2 collision estimate with both coefficients varying -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenDoubleCount
open SeedCompletionEvenDouble SeedCompletionCurveFamilies
open SeedCompletionProductGrouping AuxiliaryL2Grouping FirstDifferenceSecond

def curveConstant (d : ℕ) : ℝ := (2*d-2 : ℕ)*(8*((2*d-2 : ℕ) : ℝ)^2+3)
def withinPhase (d : ℕ) (h : Pair) (m : Pair) (z : ℕ) : ℤ := (phase d h m z : ℤ)
def indexPhase (d : ℕ) (x : Pair×(Pair×ℕ)) : ℤ := withinPhase d x.1 x.2.1 x.2.2

theorem realPolynomial_fiber_card_le_two {d : ℕ} (hd : supportedHalfDegree d)
    (h m : Pair) (B : Finset Pair) (h₁ : 0 < h.1) (h₂ : 0 < h.2) :
    (B.filter (fun n => realPolynomial d h n=realPolynomial d h m)).card ≤ 2 := by
  classical
  apply (Finset.card_le_card ?_).trans (polynomial_fiber_card_le_two hd h m B h₁ h₂)
  intro n hn
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,?_⟩
  exact Polynomial.map_injective _ (Int.cast_injective (α := ℝ)) (Finset.mem_filter.mp hn).2

theorem within_collision_card_le {d : ℕ} (hd : supportedHalfDegree d)
    (h : Pair) (hh : 0 < h.1) (ha : 0 < h.2) (B : Finset Pair) (Z : Finset ℕ)
    (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    ((collisionPairs (B ×ˢ Z) (fun p => withinPhase d h p.1 p.2)).card : ℝ) ≤
      (B.card : ℝ)*(2*(Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ))) := by
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl | rfl <;> omega
  have H := family_collision_card_bound (withinPhase d h) (realPolynomial d h) B Z
    (2*d-2) 2 (by omega)
    (fun m hm => realPolynomial_natDegree hd2 hh ha)
    (fun m hm n hn => by rw [realPolynomial_leadingCoeff hd2 hh ha,
      realPolynomial_leadingCoeff hd2 hh ha])
    (fun m hm => realPolynomial_even d h m)
    (fun m hm z w hzw => by
      change (phase d h m z : ℤ) < (phase d h m w : ℤ)
      exact_mod_cast phase_center_strictMono (m := m) hd2 hh ha hzw)
    (fun m hm z => by simpa only [withinPhase,Int.cast_natCast] using realPolynomial_eval d h m z)
    (fun m hm => realPolynomial_fiber_card_le_two hd h m B hh ha) P hP hZ
  simpa only [Nat.cast_ofNat,curveConstant] using H

def heightKey (h : Pair) : Fin 2 → ℕ := ![h.1,h.2]

theorem heightKey_injective : Function.Injective heightKey := by
  intro h g he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  exact Prod.ext h0 h1

/-- The complete actual energy, with no coefficient or height count lost. -/
theorem second_moment (d : ℕ) (hd : supportedHalfDegree d) {L ε : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ (H B : Finset Pair) (Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2) →
      (∀ z ∈ Z,0 < z ∧ (z : ℝ) ≤ P) →
      (∀ x ∈ H ×ˢ (B ×ˢ Z),((indexPhase d x).natAbs : ℝ) ≤ P^L) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ H ×ˢ (B ×ˢ Z),fourier (indexPhase d x) (α : AddCircle (1 : ℝ))‖^2) ≤
        C*P^ε*(H.card : ℝ)*(B.card : ℝ)*
          (2*(Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ))) := by
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl | rfl <;> omega
  obtain ⟨C,hC,hbound⟩ := second_moment_divisor_product 2 hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H B Z hH hZ hsize
  have hb := hbound P hP Pair (Pair×ℕ) H (B ×ˢ Z)
    (fun h x => withinPhase d h x.1 x.2) heightKey heightKey_injective.injOn (by
      intro h hh x hx
      have hp := phase_pos (m := x.1) hd2 (hH h hh).1 (hH h hh).2
        (hZ x.2 (Finset.mem_product.mp hx).2).1
      refine ⟨?_,hsize (h,x) (Finset.mem_product.mpr ⟨hh,hx⟩)⟩
      change (phase d h x.1 x.2 : ℤ) ≠ 0
      exact_mod_cast hp.ne')
    (by
      intro h hh x hx i
      fin_cases i
      · change (h.1 : ℤ) ∣ (phase d h x.1 x.2 : ℤ)
        exact_mod_cast firstHeight_dvd d h x.1 x.2
      · change (h.2 : ℤ) ∣ (phase d h x.1 x.2 : ℤ)
        exact_mod_cast secondHeight_dvd d h x.1 x.2)
  have hc : (∑ h ∈ H,((collisionPairs (B ×ˢ Z) (fun p => withinPhase d h p.1 p.2)).card : ℝ)) ≤
      (H.card : ℝ)*((B.card : ℝ)*
        (2*(Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)))) := by
    calc
      _ ≤ ∑ _h ∈ H,((B.card : ℝ)*
          (2*(Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)))) := by
        apply Finset.sum_le_sum
        intro h hh
        exact within_collision_card_le hd h (hH h hh).1 (hH h hh).2 B Z P hP
          (fun z hz => (hZ z hz).2)
      _ = _ := by simp
  exact hb.trans ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring))

#print axioms within_collision_card_le
#print axioms second_moment
end Waring.SeedCompletionEvenDoubleCount
