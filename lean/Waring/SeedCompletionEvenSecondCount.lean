import Waring.SeedCompletionEvenSecond
import Waring.SeedCompletionProductGrouping

/-! # Uniform collisions of the actual even second difference

The diagonal coefficient pairs use strict center monotonicity. Every other
pair lies on the proved coefficient-uniform even curve. Divisor grouping
then retains exactly this actual within-height collision count.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenSecondCount
open SeedCompletionEvenSecond SeedCompletionCurveUniform
open AuxiliaryL2Grouping SeedCompletionProductGrouping

def curveConstant (d : ℕ) : ℝ := (2*d-2 : ℕ)*(8*((2*d-2 : ℕ) : ℝ)^2+3)

def centerPairs (d h a m n : ℕ) (Z : Finset ℕ) : Finset (ℕ×ℕ) :=
  (Z ×ˢ Z).filter (fun z => phase d h m a z.1=phase d h n a z.2)

theorem centerPairs_diagonal {d h a : ℕ} (hd : 2 ≤ d) (hh : 0 < h)
    (ha : 0 < a) (m : ℕ) (Z : Finset ℕ) :
    (centerPairs d h a m m Z).card=Z.card := by
  have he : centerPairs d h a m m Z=Z.diag := by
    ext z
    simp only [centerPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_diag]
    constructor
    · rintro ⟨⟨hz,hw⟩,he⟩
      exact ⟨hz,(phase_center_strictMono hd hh ha).injective he⟩
    · rintro ⟨hz,he⟩
      exact ⟨⟨hz,he ▸ hz⟩,congrArg (phase d h m a) he⟩
  rw [he,Finset.diag_card]

theorem centerPairs_offdiagonal {d h a m n : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) (hmn : m ≠ n)
    (Z : Finset ℕ) (P : ℝ) (hP : 1 ≤ P)
    (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    ((centerPairs d h a m n Z).card : ℝ) ≤ curveConstant d*P^(2/3 : ℝ) := by
  have hf := realPolynomial_natDegree (m := m) hd hh ha
  have hg := realPolynomial_natDegree (m := n) hd hh ha
  have hpoints (z : ℕ×ℕ) (hz : z ∈ centerPairs d h a m n Z) :
      (realPolynomial d h m a).eval (z.1 : ℝ)=(realPolynomial d h n a).eval (z.2 : ℝ) := by
    rw [realPolynomial_eval,realPolynomial_eval]
    exact_mod_cast (Finset.mem_filter.mp hz).2
  have hinj : Set.InjOn Prod.fst (↑(centerPairs d h a m n Z) : Set (ℕ×ℕ)) := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hs : z.2=w.2 := (phase_center_strictMono hd hh ha).injective (by
      rw [← hz',← hw',he])
    exact Prod.ext he hs
  have horder : ∀ z ∈ centerPairs d h a m n Z,
      ∀ w ∈ centerPairs d h a m n Z,z.1 < w.1 → z.2 < w.2 := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have H := phase_center_strictMono (m := m) hd hh ha he
    dsimp only at H
    rw [hz',hw'] at H
    exact (phase_center_strictMono hd hh ha).lt_iff_lt.mp H
  have H := separated_even_curve_card_bound
    (f := realPolynomial d h m a) (g := realPolynomial d h n a)
    (by rw [hf]; omega) (by rw [hf,hg])
    (by rw [realPolynomial_leadingCoeff hd hh ha,realPolynomial_leadingCoeff hd hh ha])
    (realPolynomial_even d h m a) (realPolynomial_even d h n a)
    ((realPolynomial_injective hd hh ha).ne hmn)
    (centerPairs d h a m n Z) P hP (by
      intro z hz
      have hz' := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
      exact ⟨hZ z.1 hz'.1,hZ z.2 hz'.2⟩) hpoints hinj horder
  simpa only [hf,curveConstant] using H

def withinPhase (d h a : ℕ) (p : ℕ×ℕ) : ℤ := (phase d h p.1 a p.2 : ℤ)

theorem within_collision_card (d h a : ℕ) (B Z : Finset ℕ) :
    (collisionPairs (B ×ˢ Z) (withinPhase d h a)).card =
      ∑ m ∈ B, ∑ n ∈ B,(centerPairs d h a m n Z).card := by
  simp only [collisionPairs,withinPhase,centerPairs,Finset.card_eq_sum_ones,
    Finset.sum_filter,Finset.sum_product,Nat.cast_inj]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]

theorem sum_centerPairs_card_le {d h a : ℕ} (hd : 2 ≤ d) (hh : 0 < h)
    (ha : 0 < a) (B Z : Finset ℕ) {m : ℕ} (hm : m ∈ B)
    (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    (∑ n ∈ B,((centerPairs d h a m n Z).card : ℝ)) ≤
      (Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)) := by
  have hD : 0 ≤ curveConstant d*P^(2/3 : ℝ) := by unfold curveConstant; positivity
  calc
    _ ≤ ∑ n ∈ B, ((if m=n then (Z.card : ℝ) else 0)+curveConstant d*P^(2/3 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases he : m=n
      · subst n
        rw [centerPairs_diagonal hd hh ha,if_pos rfl]
        linarith
      · rw [if_neg he,zero_add]
        exact centerPairs_offdiagonal hd hh ha he Z P hP hZ
    _ = _ := by rw [Finset.sum_add_distrib]; simp [hm]

theorem within_collision_card_le {d h a : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h) (ha : 0 < a) (B Z : Finset ℕ)
    (P : ℝ) (hP : 1 ≤ P) (hZ : ∀ z ∈ Z,(z : ℝ) ≤ P) :
    ((collisionPairs (B ×ˢ Z) (withinPhase d h a)).card : ℝ) ≤
      (B.card : ℝ)*((Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ))) := by
  rw [within_collision_card,Nat.cast_sum]
  calc
    _ ≤ ∑ _m ∈ B, ((Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ))) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Nat.cast_sum]
      exact sum_centerPairs_card_le hd hh ha B Z hm P hP hZ
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

def heightKey (h : ℕ×ℕ) : Fin 2 → ℕ := ![h.1,h.2]

theorem heightKey_injective : Function.Injective heightKey := by
  intro h g he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  exact Prod.ext h0 h1

def indexPhase (d : ℕ) (x : (ℕ×ℕ)×(ℕ×ℕ)) : ℤ :=
  withinPhase d x.1.1 x.1.2 x.2

/-- Exact second-moment estimate with a uniform divisor loss. -/
theorem second_moment (d : ℕ) (hd : 2 ≤ d) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (H : Finset (ℕ×ℕ)) (B Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1 ∧ 0 < h.2) →
      (∀ z ∈ Z,0 < z ∧ (z : ℝ) ≤ P) →
      (∀ x ∈ H ×ˢ (B ×ˢ Z),((indexPhase d x).natAbs : ℝ) ≤ P^L) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ H ×ˢ (B ×ˢ Z),fourier (indexPhase d x) (α : AddCircle (1 : ℝ))‖^2) ≤
        C*P^ε*(H.card : ℝ)*(B.card : ℝ)*
          ((Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ))) := by
  obtain ⟨C,hC,hbound⟩ := second_moment_divisor_product 2 hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H B Z hH hZ hsize
  have hb := hbound P hP (ℕ×ℕ) (ℕ×ℕ) H (B ×ˢ Z)
    (fun h => withinPhase d h.1 h.2) heightKey heightKey_injective.injOn (by
      intro h hh x hx
      have hp := phase_pos (m := x.1) hd (hH h hh).1 (hH h hh).2
        (hZ x.2 (Finset.mem_product.mp hx).2).1
      refine ⟨?_,hsize (h,x) (Finset.mem_product.mpr ⟨hh,hx⟩)⟩
      change (phase d h.1 x.1 h.2 x.2 : ℤ) ≠ 0
      exact_mod_cast hp.ne')
    (by
      intro h hh x hx i
      fin_cases i
      · change (h.1 : ℤ) ∣ (phase d h.1 x.1 h.2 x.2 : ℤ)
        exact_mod_cast height_dvd d h.1 x.1 h.2 x.2
      · change (h.2 : ℤ) ∣ (phase d h.1 x.1 h.2 x.2 : ℤ)
        exact_mod_cast secondHeight_dvd d h.1 x.1 h.2 x.2)
  have hc : (∑ h ∈ H,((collisionPairs (B ×ˢ Z) (withinPhase d h.1 h.2)).card : ℝ)) ≤
      (H.card : ℝ)*((B.card : ℝ)*
        ((Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)))) := by
    calc
      _ ≤ ∑ _h ∈ H,((B.card : ℝ)*
          ((Z.card : ℝ)+(B.card : ℝ)*(curveConstant d*P^(2/3 : ℝ)))) := by
        apply Finset.sum_le_sum
        intro h hh
        exact within_collision_card_le hd (hH h hh).1 (hH h hh).2 B Z P hP
          (fun z hz => (hZ z hz).2)
      _ = _ := by simp
  exact hb.trans ((mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring))

#print axioms centerPairs_offdiagonal
#print axioms within_collision_card_le
#print axioms second_moment
end Waring.SeedCompletionEvenSecondCount
