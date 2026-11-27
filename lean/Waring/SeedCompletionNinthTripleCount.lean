import Waring.SeedCompletionNinthTriple
import Waring.SeedCompletionProductGrouping

/-! # Actual degree-nine third-phase energy with two varying coefficients -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthTripleCount
open SeedCompletionNinthTriple SeedCompletionCurveFamilies
open SeedCompletionProductGrouping AuxiliaryL2Grouping
open SeedCompletionNinthDouble (Pair)

def withinPhase (h : Heights) (m : Pair) (z : ℕ) : ℤ := (phase h m z : ℤ)
def indexPhase (x : Heights×(Pair×ℕ)) : ℤ := withinPhase x.1 x.2.1 x.2.2

theorem realPolynomial_fiber_card_le_two (h : Heights) (m : Pair) (B : Finset Pair)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (B.filter (fun n => realPolynomial h n=realPolynomial h m)).card ≤ 2 := by
  classical
  apply (Finset.card_le_card ?_).trans (polynomial_fiber_card_le_two h m B h₁ h₂ h₃)
  intro n hn
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1,?_⟩
  exact Polynomial.map_injective _ (Int.cast_injective (α := ℝ)) (Finset.mem_filter.mp hn).2

theorem within_collision_card_le (h : Heights) (h₁ : 0 < h.1.1)
    (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) (B : Finset Pair) (Z : Finset ℕ)
    (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    ((collisionPairs (B ×ˢ Z) (fun p => withinPhase h p.1 p.2)).card : ℝ) ≤
      (B.card : ℝ)*(2*(Z.card : ℝ)+(B.card : ℝ)*(1746*P^(2/3 : ℝ))) := by
  have H := family_collision_card_bound (withinPhase h) (realPolynomial h) B Z 6 2 (by norm_num)
    (fun m hm => realPolynomial_natDegree h₁ h₂ h₃)
    (fun m hm n hn => by rw [realPolynomial_leadingCoeff h₁ h₂ h₃,
      realPolynomial_leadingCoeff h₁ h₂ h₃])
    (fun m hm => realPolynomial_even h m)
    (fun m hm z w hzw => by
      change (phase h m z : ℤ) < (phase h m w : ℤ)
      exact_mod_cast phase_center_strictMono (m := m) h₁ h₂ h₃ hzw)
    (fun m hm z => by simpa only [withinPhase,Int.cast_natCast] using realPolynomial_eval h m z)
    (fun m hm => realPolynomial_fiber_card_le_two h m B h₁ h₂ h₃) P hP hZ
  norm_num only [Nat.cast_ofNat,show (6 : ℝ)*(8*6^2+3)=1746 by norm_num] at H
  exact H

def heightKey (h : Heights) : Fin 3 → ℕ := ![h.1.1,h.1.2,h.2]

theorem heightKey_injective : Function.Injective heightKey := by
  intro h g he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  exact Prod.ext (Prod.ext h0 h1) h2

theorem second_moment {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ (H : Finset Heights) (B : Finset Pair) (Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1.1 ∧ 0 < h.1.2 ∧ 0 < h.2) →
      (∀ z ∈ Z,0 < z ∧ (z : ℝ) ≤ P) →
      (∀ x ∈ H ×ˢ (B ×ˢ Z),((indexPhase x).natAbs : ℝ) ≤ P^L) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ H ×ˢ (B ×ˢ Z),fourier (indexPhase x) (α : AddCircle (1 : ℝ))‖^2) ≤
        C*P^ε*(H.card : ℝ)*(B.card : ℝ)*
          (2*(Z.card : ℝ)+(B.card : ℝ)*(1746*P^(2/3 : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := second_moment_divisor_product 3 hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H B Z hH hZ hsize
  have hb := hbound P hP Heights (Pair×ℕ) H (B ×ˢ Z)
    (fun h x => withinPhase h x.1 x.2) heightKey heightKey_injective.injOn (by
      intro h hh x hx
      have hp := phase_pos (m := x.1) (hH h hh).1 (hH h hh).2.1 (hH h hh).2.2
        (hZ x.2 (Finset.mem_product.mp hx).2).1
      refine ⟨?_,hsize (h,x) (Finset.mem_product.mpr ⟨hh,hx⟩)⟩
      change (phase h x.1 x.2 : ℤ) ≠ 0
      exact_mod_cast hp.ne')
    (by
      intro h hh x hx i
      fin_cases i
      · change (h.1.1 : ℤ) ∣ (phase h x.1 x.2 : ℤ)
        exact_mod_cast firstHeight_dvd h x.1 x.2
      · change (h.1.2 : ℤ) ∣ (phase h x.1 x.2 : ℤ)
        exact_mod_cast secondHeight_dvd h x.1 x.2
      · change (h.2 : ℤ) ∣ (phase h x.1 x.2 : ℤ)
        exact_mod_cast thirdHeight_dvd h x.1 x.2)
  have hc : (∑ h ∈ H,((collisionPairs (B ×ˢ Z) (fun p => withinPhase h p.1 p.2)).card : ℝ)) ≤
      (H.card : ℝ)*((B.card : ℝ)*
        (2*(Z.card : ℝ)+(B.card : ℝ)*(1746*P^(2/3 : ℝ)))) := by
    calc
      _ ≤ ∑ _h ∈ H,((B.card : ℝ)*
          (2*(Z.card : ℝ)+(B.card : ℝ)*(1746*P^(2/3 : ℝ)))) := by
        apply Finset.sum_le_sum
        intro h hh
        exact within_collision_card_le h (hH h hh).1 (hH h hh).2.1 (hH h hh).2.2 B Z P hP
          (fun z hz => (hZ z hz).2)
      _ = _ := by simp
  exact hb.trans ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring))

#print axioms within_collision_card_le
#print axioms second_moment
end Waring.SeedCompletionNinthTripleCount
