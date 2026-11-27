import Waring.SeedCompletionEvenDoubleIdentity
import Waring.SeedCompletionCurveParityFamilies

/-! # Even third differences with two varying coefficient blocks

The newest coefficient is one. The resulting center polynomial has odd
parity and positive coefficients. Its first two nonleading coefficients
determine the two old positive amplitudes up to interchange.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenTriple
open IntegerDifferencePolynomial Polynomial FirstDifferenceSecond
open SeedCompletionEvenDouble (Pair amplitude)

abbrev Heights := Pair × ℕ

def exponent (d i j l : ℕ) : ℕ := 2*d-(2*i+1)-(2*j+1)-(2*l+1)
def coefficient (d : ℕ) (h : Heights) (m : Pair) (i j l : ℕ) : ℕ :=
  8*(2*d).choose (2*i+1)*(2*d-(2*i+1)).choose (2*j+1)*
    (2*d-(2*i+1)-(2*j+1)).choose (2*l+1)*
    h.1.1^(2*i+1)*h.1.2^(2*j+1)*h.2^(2*l+1)*
    m.1^(2*d*(2*i))*m.2^(2*d*(2*j))
def phase (d : ℕ) (h : Heights) (m : Pair) (z : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d-1),∑ j ∈ Finset.range (d-i-1),
    ∑ l ∈ Finset.range (d-i-j-1),coefficient d h m i j l*z^(exponent d i j l)
def phasePolynomial (d : ℕ) (h : Heights) (m : Pair) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (d-1),∑ j ∈ Finset.range (d-i-1),
    ∑ l ∈ Finset.range (d-i-j-1),
      monomial (exponent d i j l) ((coefficient d h m i j l : ℕ) : ℤ)
def realPolynomial (d : ℕ) (h : Heights) (m : Pair) : Polynomial ℝ :=
  (phasePolynomial d h m).map (Int.castRingHom ℝ)

theorem phasePolynomial_eval (d : ℕ) (h : Heights) (m : Pair) (z : ℕ) :
    (phasePolynomial d h m).eval (z : ℤ)=(phase d h m z : ℤ) := by
  simp [phasePolynomial,phase,Polynomial.eval_finset_sum,Polynomial.eval_monomial]

theorem realPolynomial_eval (d : ℕ) (h : Heights) (m : Pair) (z : ℕ) :
    (realPolynomial d h m).eval (z : ℝ)=(phase d h m z : ℝ) := by
  unfold realPolynomial
  rw [Polynomial.eval_map]
  have H := congrArg (fun n : ℤ => (n : ℝ)) (phasePolynomial_eval d h m z)
  change (Int.castRingHom ℝ) ((phasePolynomial d h m).eval (z : ℤ)) = _ at H
  rw [← Polynomial.eval₂_at_apply] at H
  simpa only [Int.cast_natCast] using H

theorem coefficient_zero_zero_zero (d : ℕ) (h : Heights) (m : Pair) :
    coefficient d h m 0 0 0=8*(2*d)*(2*d-1)*(2*d-2)*h.1.1*h.1.2*h.2 := by
  simp [coefficient,Nat.sub_sub]

theorem phase_pos {d : ℕ} {h : Heights} {m : Pair} {z : ℕ} (hd : 2 ≤ d)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) (hz : 0 < z) :
    0 < phase d h m z := by
  unfold phase
  apply Finset.sum_pos'
  · intro i hi; exact Nat.zero_le _
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_pos'
    · intro j hj; exact Nat.zero_le _
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      apply Finset.sum_pos'
      · intro l hl; exact Nat.zero_le _
      · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
        rw [coefficient_zero_zero_zero]
        have hk1 : 0 < 2*d-1 := by omega
        have hk2 : 0 < 2*d-2 := by omega
        positivity

theorem firstHeight_dvd (d : ℕ) (h : Heights) (m : Pair) (z : ℕ) :
    h.1.1 ∣ phase d h m z := by
  unfold phase
  apply Finset.dvd_sum; intro i hi
  apply Finset.dvd_sum; intro j hj
  apply Finset.dvd_sum; intro l hl
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self h.1.1 (by omega : 2*i+1 ≠ 0)) _

theorem secondHeight_dvd (d : ℕ) (h : Heights) (m : Pair) (z : ℕ) :
    h.1.2 ∣ phase d h m z := by
  unfold phase
  apply Finset.dvd_sum; intro i hi
  apply Finset.dvd_sum; intro j hj
  apply Finset.dvd_sum; intro l hl
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self h.1.2 (by omega : 2*j+1 ≠ 0)) _

theorem thirdHeight_dvd (d : ℕ) (h : Heights) (m : Pair) (z : ℕ) :
    h.2 ∣ phase d h m z := by
  unfold phase
  apply Finset.dvd_sum; intro i hi
  apply Finset.dvd_sum; intro j hj
  apply Finset.dvd_sum; intro l hl
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self h.2 (by omega : 2*l+1 ≠ 0)) _

theorem phase_center_strictMono {d : ℕ} {h : Heights} {m : Pair} (hd : 2 ≤ d)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    StrictMono (phase d h m) := by
  intro z w hzw
  unfold phase
  apply Finset.sum_lt_sum
  · intro i hi
    apply Finset.sum_le_sum; intro j hj
    apply Finset.sum_le_sum; intro l hl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_lt_sum
    · intro j hj
      apply Finset.sum_le_sum; intro l hl
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      apply Finset.sum_lt_sum
      · intro l hl
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
      · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
        rw [coefficient_zero_zero_zero]
        have hc : 0 < 8*(2*d)*(2*d-1)*(2*d-2)*h.1.1*h.1.2*h.2 := by
          have hk1 : 0 < 2*d-1 := by omega
          have hk2 : 0 < 2*d-2 := by omega
          positivity
        exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hzw
          (by unfold exponent; omega)) hc

theorem phasePolynomial_natDegree_le (d : ℕ) (h : Heights) (m : Pair) :
    (phasePolynomial d h m).natDegree ≤ 2*d-3 := by
  unfold phasePolynomial
  apply natDegree_sum_le_of_forall_le; intro i hi
  apply natDegree_sum_le_of_forall_le; intro j hj
  apply natDegree_sum_le_of_forall_le; intro l hl
  exact (natDegree_monomial_le _).trans (by unfold exponent; omega)

theorem realPolynomial_odd (d : ℕ) (h : Heights) (m : Pair) (t : ℝ) :
    (realPolynomial d h m).eval (-t)= -(realPolynomial d h m).eval t := by
  unfold realPolynomial phasePolynomial
  simp only [Polynomial.map_sum,Polynomial.eval_finset_sum,map_monomial,eval_monomial,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro l hl
  have hi := Finset.mem_range.mp hi
  have hj := Finset.mem_range.mp hj
  have hl := Finset.mem_range.mp hl
  have he : exponent d i j l=2*(d-i-j-l-2)+1 := by unfold exponent; omega
  rw [he,(odd_two_mul_add_one _).neg_pow]
  ring

theorem phasePolynomial_coeff_top {d : ℕ} (hd : 2 ≤ d) (h : Heights) (m : Pair) :
    (phasePolynomial d h m).coeff (2*d-3)=
      ((8*(2*d)*(2*d-1)*(2*d-2)*h.1.1*h.1.2*h.2 : ℕ) : ℤ) := by
  unfold phasePolynomial
  simp only [finset_sum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · rw [Finset.sum_eq_single 0]
      · rw [show exponent d 0 0 0=2*d-3 by unfold exponent; omega,
          coeff_monomial,if_pos rfl,coefficient_zero_zero_zero]
      · intro l hl hl0
        rw [coeff_monomial,if_neg]
        unfold exponent; omega
      · intro hbad
        exact False.elim (hbad (Finset.mem_range.mpr (by omega)))
    · intro j hj hj0
      apply Finset.sum_eq_zero; intro l hl
      rw [coeff_monomial,if_neg]
      unfold exponent; omega
    · intro hbad
      exact False.elim (hbad (Finset.mem_range.mpr (by omega)))
  · intro i hi hi0
    apply Finset.sum_eq_zero; intro j hj
    apply Finset.sum_eq_zero; intro l hl
    rw [coeff_monomial,if_neg]
    unfold exponent; omega
  · intro hbad
    exact False.elim (hbad (Finset.mem_range.mpr (by omega)))

theorem phasePolynomial_natDegree {d : ℕ} {h : Heights} {m : Pair} (hd : 2 ≤ d)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (phasePolynomial d h m).natDegree=2*d-3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (phasePolynomial_natDegree_le d h m)
  rw [phasePolynomial_coeff_top hd]
  have hk1 : 0 < 2*d-1 := by omega
  have hk2 : 0 < 2*d-2 := by omega
  positivity

theorem realPolynomial_natDegree {d : ℕ} {h : Heights} {m : Pair} (hd : 2 ≤ d)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (realPolynomial d h m).natDegree=2*d-3 := by
  rw [realPolynomial,natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),
    phasePolynomial_natDegree hd h₁ h₂ h₃]

theorem realPolynomial_leadingCoeff {d : ℕ} {h : Heights} {m : Pair} (hd : 2 ≤ d)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (realPolynomial d h m).leadingCoeff=
      ((8*(2*d)*(2*d-1)*(2*d-2)*h.1.1*h.1.2*h.2 : ℕ) : ℝ) := by
  rw [realPolynomial,leadingCoeff_map' (Int.cast_injective (α := ℝ)),
    leadingCoeff,phasePolynomial_natDegree hd h₁ h₂ h₃,phasePolynomial_coeff_top hd]
  rfl

def middleCoefficient (d : ℕ) : ℕ := 8*(2*d).choose 3*(2*d-3)*(2*d-4)
def lowCoefficient (d : ℕ) : ℕ := 8*(2*d).choose 5*(2*d-5)*(2*d-6)/3

set_option maxHeartbeats 1600000 in
theorem phasePolynomial_coeff_middle {d : ℕ} (hd : supportedHalfDegree d)
    (h : Heights) (m : Pair) :
    (phasePolynomial d h m).coeff (2*d-5)=
      (h.1.1*h.1.2*h.2*middleCoefficient d*
        ((amplitude d h.1 m).1^2+(amplitude d h.1 m).2^2+h.2^2) : ℕ) := by
  simp only [phasePolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  rcases hd with rfl | rfl | rfl <;>
    norm_num [exponent,Finset.sum_range_succ] <;>
    norm_num [coefficient,Nat.choose,amplitude,middleCoefficient] <;> ring

set_option maxHeartbeats 1600000 in
theorem phasePolynomial_coeff_low {d : ℕ} (hd : supportedHalfDegree d)
    (h : Heights) (m : Pair) :
    (phasePolynomial d h m).coeff (2*d-7)=
      (h.1.1*h.1.2*h.2*lowCoefficient d*
        (3*((amplitude d h.1 m).1^4+(amplitude d h.1 m).2^4+h.2^4)+
        10*((amplitude d h.1 m).1^2*(amplitude d h.1 m).2^2+
          ((amplitude d h.1 m).1^2+(amplitude d h.1 m).2^2)*h.2^2)) : ℕ) := by
  simp only [phasePolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  rcases hd with rfl | rfl | rfl <;>
    norm_num [exponent,Finset.sum_range_succ] <;>
    norm_num [coefficient,Nat.choose,amplitude,lowCoefficient] <;> ring

theorem amplitude_eq_or_swap {d : ℕ} (hd : supportedHalfDegree d)
    {h : Heights} {m n : Pair} (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2)
    (he : phasePolynomial d h m=phasePolynomial d h n) :
    amplitude d h.1 m=amplitude d h.1 n ∨
      amplitude d h.1 m=((amplitude d h.1 n).2,(amplitude d h.1 n).1) := by
  have hcM := congrArg (fun p : Polynomial ℤ => p.coeff (2*d-5)) he
  dsimp only at hcM
  rw [phasePolynomial_coeff_middle hd,phasePolynomial_coeff_middle hd] at hcM
  have hM : h.1.1*h.1.2*h.2*middleCoefficient d*
      ((amplitude d h.1 m).1^2+(amplitude d h.1 m).2^2+h.2^2) =
      h.1.1*h.1.2*h.2*middleCoefficient d*
      ((amplitude d h.1 n).1^2+(amplitude d h.1 n).2^2+h.2^2) := by exact_mod_cast hcM
  have hmid : 0 < middleCoefficient d := by
    rcases hd with rfl | rfl | rfl <;> norm_num [middleCoefficient,Nat.choose]
  have hlow : 0 < lowCoefficient d := by
    rcases hd with rfl | rfl | rfl <;> norm_num [lowCoefficient,Nat.choose]
  have hs' := Nat.eq_of_mul_eq_mul_left
    (by positivity : 0 < h.1.1*h.1.2*h.2*middleCoefficient d) hM
  have hs : (amplitude d h.1 m).1^2+(amplitude d h.1 m).2^2 =
      (amplitude d h.1 n).1^2+(amplitude d h.1 n).2^2 := by omega
  have hcL := congrArg (fun p : Polynomial ℤ => p.coeff (2*d-7)) he
  dsimp only at hcL
  rw [phasePolynomial_coeff_low hd,phasePolynomial_coeff_low hd] at hcL
  have hL : h.1.1*h.1.2*h.2*lowCoefficient d*
      (3*((amplitude d h.1 m).1^4+(amplitude d h.1 m).2^4+h.2^4)+
      10*((amplitude d h.1 m).1^2*(amplitude d h.1 m).2^2+
        ((amplitude d h.1 m).1^2+(amplitude d h.1 m).2^2)*h.2^2)) =
      h.1.1*h.1.2*h.2*lowCoefficient d*
      (3*((amplitude d h.1 n).1^4+(amplitude d h.1 n).2^4+h.2^4)+
      10*((amplitude d h.1 n).1^2*(amplitude d h.1 n).2^2+
        ((amplitude d h.1 n).1^2+(amplitude d h.1 n).2^2)*h.2^2)) := by exact_mod_cast hcL
  have hL' := Nat.eq_of_mul_eq_mul_left
    (by positivity : 0 < h.1.1*h.1.2*h.2*lowCoefficient d) hL
  have hprod : (amplitude d h.1 m).1^2*(amplitude d h.1 m).2^2 =
      (amplitude d h.1 n).1^2*(amplitude d h.1 n).2^2 := by
    rw [hs] at hL'
    nlinarith [congrArg (fun t : ℕ => t^2) hs]
  rcases SeedCompletionNinthDouble.pair_eq_or_swap_of_sum_prod hs hprod with hp | hp
  · exact Or.inl (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.2))
  · exact Or.inr (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.2))

theorem polynomial_fiber_card_le_two {d : ℕ} (hd : supportedHalfDegree d)
    (h : Heights) (m : Pair) (B : Finset Pair)
    (h₁ : 0 < h.1.1) (h₂ : 0 < h.1.2) (h₃ : 0 < h.2) :
    (B.filter (fun n => phasePolynomial d h n=phasePolynomial d h m)).card ≤ 2 := by
  classical
  have hd0 : 0 < d := by rcases hd with rfl | rfl | rfl <;> omega
  let F := B.filter (fun n => phasePolynomial d h n=phasePolynomial d h m)
  have hs : F.image (amplitude d h.1) ⊆
      {amplitude d h.1 m,((amplitude d h.1 m).2,(amplitude d h.1 m).1)} := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    rcases amplitude_eq_or_swap hd h₁ h₂ h₃ (Finset.mem_filter.mp hn).2 with he | he
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  calc
    _ = (F.image (amplitude d h.1)).card := by
      symm
      exact Finset.card_image_iff.mpr
        (SeedCompletionEvenDouble.amplitude_injective hd0 h₁ h₂).injOn
    _ ≤ ({amplitude d h.1 m,((amplitude d h.1 m).2,(amplitude d h.1 m).1)} : Finset Pair).card :=
      Finset.card_le_card hs
    _ ≤ 2 := Finset.card_le_two

#print axioms realPolynomial_odd
#print axioms phasePolynomial_coeff_middle
#print axioms phasePolynomial_coeff_low
#print axioms polynomial_fiber_card_le_two
end Waring.SeedCompletionEvenTriple
