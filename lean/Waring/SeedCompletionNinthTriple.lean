import Waring.SeedCompletionNinthDouble
import Waring.SeedCompletionCurveFamilies
import Waring.SeedCompletionEvenSecond

/-! # The actual degree-nine third phase with newest coefficient one

Its even center polynomial has degree six. The two remaining coefficient
amplitudes are determined up to interchange by its next two coefficients.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthTriple
open IntegerDifferencePolynomial Polynomial
open SeedCompletionNinthDouble (Pair amplitude)

abbrev Heights := Pair×ℕ

def leadingFactor (h : Heights) : ℕ := 192*h.1.1*h.1.2*h.2

def middle (h : Heights) (m : Pair) : ℕ :=
  105*h.2^2+105*((amplitude h.1 m).1^2+(amplitude h.1 m).2^2)
def low (h : Heights) (m : Pair) : ℕ :=
  63*h.2^4+210*((amplitude h.1 m).1^2+(amplitude h.1 m).2^2)*h.2^2+
    63*((amplitude h.1 m).1^4+(amplitude h.1 m).2^4)+
    210*(amplitude h.1 m).1^2*(amplitude h.1 m).2^2

def constant (h : Heights) (m : Pair) : ℕ :=
  3*h.2^6+21*((amplitude h.1 m).1^2+(amplitude h.1 m).2^2)*h.2^4+
    (21*((amplitude h.1 m).1^4+(amplitude h.1 m).2^4)+
      70*(amplitude h.1 m).1^2*(amplitude h.1 m).2^2)*h.2^2+
    3*((amplitude h.1 m).1^6+(amplitude h.1 m).2^6)+
      21*((amplitude h.1 m).1^4*(amplitude h.1 m).2^2+
        (amplitude h.1 m).1^2*(amplitude h.1 m).2^4)

def phase (h : Heights) (m : Pair) (z : ℕ) : ℕ :=
  leadingFactor h*(21*z^6+middle h m*z^4+low h m*z^2+constant h m)

def phasePolynomial (h : Heights) (m : Pair) : Polynomial ℤ :=
  monomial 6 ((leadingFactor h*21 : ℕ) : ℤ)+
  monomial 4 ((leadingFactor h*middle h m : ℕ) : ℤ)+
  monomial 2 ((leadingFactor h*low h m : ℕ) : ℤ)+
  monomial 0 ((leadingFactor h*constant h m : ℕ) : ℤ)

def realPolynomial (h : Heights) (m : Pair) : Polynomial ℝ :=
  (phasePolynomial h m).map (Int.castRingHom ℝ)

theorem phasePolynomial_eval (h : Heights) (m : Pair) (z : ℕ) :
    (phasePolynomial h m).eval (z : ℤ)=(phase h m z : ℤ) := by
  simp only [phasePolynomial,Polynomial.eval_add,Polynomial.eval_monomial,phase]
  push_cast
  ring

theorem realPolynomial_eval (h : Heights) (m : Pair) (z : ℕ) :
    (realPolynomial h m).eval (z : ℝ)=(phase h m z : ℝ) := by
  unfold realPolynomial
  rw [Polynomial.eval_map]
  have H := congrArg (fun n : ℤ => (n : ℝ)) (phasePolynomial_eval h m z)
  change (Int.castRingHom ℝ) ((phasePolynomial h m).eval (z : ℤ)) = _ at H
  rw [← Polynomial.eval₂_at_apply] at H
  simpa only [Int.cast_natCast] using H

theorem phase_pos {h : Heights} {m : Pair} {z : ℕ}
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) (hz : 0 < z) :
    0 < phase h m z := by unfold phase leadingFactor; positivity

theorem firstHeight_dvd (h : Heights) (m : Pair) (z : ℕ) : h.1.1 ∣ phase h m z := by
  unfold phase leadingFactor
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_left h.1.1 192) h.1.2) h.2) _

theorem secondHeight_dvd (h : Heights) (m : Pair) (z : ℕ) : h.1.2 ∣ phase h m z := by
  unfold phase leadingFactor
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left h.1.2 _) h.2) _

theorem thirdHeight_dvd (h : Heights) (m : Pair) (z : ℕ) : h.2 ∣ phase h m z := by
  unfold phase leadingFactor
  exact dvd_mul_of_dvd_left (dvd_mul_left h.2 _) _

theorem phase_center_strictMono {h : Heights} {m : Pair}
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) : StrictMono (phase h m) := by
  intro z w hzw
  unfold phase
  apply Nat.mul_lt_mul_of_pos_left _ (by unfold leadingFactor; positivity)
  have h6 := Nat.pow_lt_pow_left hzw (by norm_num : 6 ≠ 0)
  have h4 := Nat.pow_le_pow_left hzw.le 4
  have h2 := Nat.pow_le_pow_left hzw.le 2
  nlinarith [Nat.mul_le_mul_left (middle h m) h4,Nat.mul_le_mul_left (low h m) h2]

theorem realPolynomial_even (h : Heights) (m : Pair) (t : ℝ) :
    (realPolynomial h m).eval (-t)=(realPolynomial h m).eval t := by
  simp only [realPolynomial,phasePolynomial,Polynomial.map_add,Polynomial.map_monomial,
    Polynomial.eval_add,Polynomial.eval_monomial]
  ring

theorem phasePolynomial_natDegree {h : Heights} {m : Pair}
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (phasePolynomial h m).natDegree=6 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold phasePolynomial
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact (Polynomial.natDegree_add_le _ _).trans
          (max_le (Polynomial.natDegree_monomial_le _)
            ((Polynomial.natDegree_monomial_le _).trans (by norm_num)))
      · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
    · exact (Polynomial.natDegree_monomial_le _).trans (by norm_num)
  · simp only [phasePolynomial,Polynomial.coeff_add,Polynomial.coeff_monomial]
    norm_num
    unfold leadingFactor
    positivity

theorem realPolynomial_natDegree {h : Heights} {m : Pair}
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (realPolynomial h m).natDegree=6 := by
  rw [realPolynomial,natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),
    phasePolynomial_natDegree h₁ h₂ h₃]

theorem realPolynomial_leadingCoeff {h : Heights} {m : Pair}
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (realPolynomial h m).leadingCoeff=((leadingFactor h*21 : ℕ) : ℝ) := by
  rw [realPolynomial,leadingCoeff_map' (Int.cast_injective (α := ℝ)),
    leadingCoeff,phasePolynomial_natDegree h₁ h₂ h₃]
  simp [phasePolynomial,Polynomial.coeff_monomial]

theorem amplitude_eq_or_swap {h : Heights} {m n : Pair}
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2)
    (he : phasePolynomial h m=phasePolynomial h n) :
    amplitude h.1 m=amplitude h.1 n ∨
      amplitude h.1 m=((amplitude h.1 n).2,(amplitude h.1 n).1) := by
  have hc4 := congrArg (fun p : Polynomial ℤ => p.coeff 4) he
  have hc2 := congrArg (fun p : Polynomial ℤ => p.coeff 2) he
  simp only [phasePolynomial,Polynomial.coeff_add,Polynomial.coeff_monomial] at hc4 hc2
  norm_num only at hc4 hc2
  simp only [if_false,if_true,zero_add,add_zero] at hc4 hc2
  have hm : leadingFactor h*middle h m=leadingFactor h*middle h n := by exact_mod_cast hc4
  have hl : leadingFactor h*low h m=leadingFactor h*low h n := by exact_mod_cast hc2
  have hL : 0 < leadingFactor h := by unfold leadingFactor; positivity
  have hm' := Nat.eq_of_mul_eq_mul_left hL hm
  have hl' := Nat.eq_of_mul_eq_mul_left hL hl
  have hs : (amplitude h.1 m).1^2+(amplitude h.1 m).2^2 =
      (amplitude h.1 n).1^2+(amplitude h.1 n).2^2 := by
    unfold middle at hm'
    omega
  have hprod : (amplitude h.1 m).1^2*(amplitude h.1 m).2^2 =
      (amplitude h.1 n).1^2*(amplitude h.1 n).2^2 := by
    unfold low at hl'
    rw [hs] at hl'
    nlinarith [congrArg (fun t : ℕ => t^2) hs]
  rcases SeedCompletionNinthDouble.pair_eq_or_swap_of_sum_prod hs hprod with hp | hp
  · exact Or.inl (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.2))
  · exact Or.inr (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.2))

theorem polynomial_fiber_card_le_two (h : Heights) (m : Pair) (B : Finset Pair)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (B.filter (fun n => phasePolynomial h n=phasePolynomial h m)).card ≤ 2 := by
  classical
  let F := B.filter (fun n => phasePolynomial h n=phasePolynomial h m)
  have hs : F.image (amplitude h.1) ⊆
      {amplitude h.1 m,((amplitude h.1 m).2,(amplitude h.1 m).1)} := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    rcases amplitude_eq_or_swap h₁ h₂ h₃ (Finset.mem_filter.mp hn).2 with he | he
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  calc
    _ = (F.image (amplitude h.1)).card := by
      symm
      exact Finset.card_image_iff.mpr (SeedCompletionNinthDouble.amplitude_injective h₁ h₂).injOn
    _ ≤ ({amplitude h.1 m,((amplitude h.1 m).2,(amplitude h.1 m).1)} : Finset Pair).card :=
      Finset.card_le_card hs
    _ ≤ 2 := Finset.card_le_two

#print axioms phase_center_strictMono
#print axioms polynomial_fiber_card_le_two
end Waring.SeedCompletionNinthTriple
