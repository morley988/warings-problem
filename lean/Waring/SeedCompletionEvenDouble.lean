import Waring.SeedCompletionEvenSecond
import Waring.SeedCompletionNinthDouble

/-! # Even second differences with both coefficients varying

The two normalized coefficients are retained in the actual source phase.
Two nonleading coefficients determine their positive amplitudes up to
interchange, and hence full center-polynomial fibers contain at most two
coefficient pairs.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionEvenDouble
open IntegerDifferencePolynomial Polynomial FirstDifferenceSecond
abbrev Pair := ℕ×ℕ

def exponent (d i j : ℕ) : ℕ := 2*d-(2*i+1)-(2*j+1)
def coefficient (d : ℕ) (h m : Pair) (i j : ℕ) : ℕ :=
  4*(2*d).choose (2*i+1)*(2*d-(2*i+1)).choose (2*j+1)*
    h.1^(2*i+1)*h.2^(2*j+1)*m.1^(2*d*(2*i))*m.2^(2*d*(2*j))
def phase (d : ℕ) (h m : Pair) (z : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d,∑ j ∈ Finset.range (d-i),
    coefficient d h m i j*z^(exponent d i j)
def phasePolynomial (d : ℕ) (h m : Pair) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d,∑ j ∈ Finset.range (d-i),
    monomial (exponent d i j) ((coefficient d h m i j : ℕ) : ℤ)
def realPolynomial (d : ℕ) (h m : Pair) : Polynomial ℝ :=
  (phasePolynomial d h m).map (Int.castRingHom ℝ)
def amplitude (d : ℕ) (h m : Pair) : Pair := (h.1*m.1^(2*d),h.2*m.2^(2*d))

theorem phasePolynomial_eval (d : ℕ) (h m : Pair) (z : ℕ) :
    (phasePolynomial d h m).eval (z : ℤ)=(phase d h m z : ℤ) := by
  simp [phasePolynomial,phase,Polynomial.eval_finset_sum,Polynomial.eval_monomial]

theorem realPolynomial_eval (d : ℕ) (h m : Pair) (z : ℕ) :
    (realPolynomial d h m).eval (z : ℝ)=(phase d h m z : ℝ) := by
  unfold realPolynomial
  rw [Polynomial.eval_map]
  have H := congrArg (fun n : ℤ => (n : ℝ)) (phasePolynomial_eval d h m z)
  change (Int.castRingHom ℝ) ((phasePolynomial d h m).eval (z : ℤ)) = _ at H
  rw [← Polynomial.eval₂_at_apply] at H
  simpa only [Int.cast_natCast] using H

theorem coefficient_zero_zero (d : ℕ) (h m : Pair) :
    coefficient d h m 0 0=4*(2*d)*(2*d-1)*h.1*h.2 := by simp [coefficient]

theorem phase_pos {d : ℕ} {h m : Pair} {z : ℕ} (hd : 2 ≤ d)
    (hh : 0 < h.1) (ha : 0 < h.2) (hz : 0 < z) : 0 < phase d h m z := by
  unfold phase
  apply Finset.sum_pos'
  · intro i hi
    exact Nat.zero_le _
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_pos'
    · intro j hj
      exact Nat.zero_le _
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      rw [coefficient_zero_zero]
      have hk : 0 < 2*d-1 := by omega
      positivity

theorem firstHeight_dvd (d : ℕ) (h m : Pair) (z : ℕ) : h.1 ∣ phase d h m z := by
  unfold phase
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self h.1 (by omega : 2*i+1 ≠ 0)) _

theorem secondHeight_dvd (d : ℕ) (h m : Pair) (z : ℕ) : h.2 ∣ phase d h m z := by
  unfold phase
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  unfold coefficient
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  exact dvd_mul_of_dvd_right (dvd_pow_self h.2 (by omega : 2*j+1 ≠ 0)) _

theorem phase_center_strictMono {d : ℕ} {h m : Pair} (hd : 2 ≤ d)
    (hh : 0 < h.1) (ha : 0 < h.2) : StrictMono (phase d h m) := by
  intro z w hzw
  unfold phase
  apply Finset.sum_lt_sum
  · intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
  · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
    apply Finset.sum_lt_sum
    · intro j hj
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hzw.le _)
    · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
      rw [coefficient_zero_zero]
      have hc : 0 < 4*(2*d)*(2*d-1)*h.1*h.2 := by
        have hk : 0 < 2*d-1 := by omega
        positivity
      exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hzw
        (by unfold exponent; omega)) hc

theorem phasePolynomial_natDegree_le (d : ℕ) (h m : Pair) :
    (phasePolynomial d h m).natDegree ≤ 2*d-2 := by
  unfold phasePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by unfold exponent; omega)

theorem realPolynomial_even (d : ℕ) (h m : Pair) (t : ℝ) :
    (realPolynomial d h m).eval (-t)=(realPolynomial d h m).eval t := by
  unfold realPolynomial phasePolynomial
  simp only [Polynomial.map_sum,Polynomial.eval_finset_sum,map_monomial,eval_monomial]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi := Finset.mem_range.mp hi
  have hj := Finset.mem_range.mp hj
  have he : exponent d i j=2*(d-i-j-1) := by unfold exponent; omega
  rw [he,pow_mul,pow_mul]
  simp

theorem phasePolynomial_coeff_top {d : ℕ} (hd : 2 ≤ d) (h m : Pair) :
    (phasePolynomial d h m).coeff (2*d-2)=
      ((4*(2*d)*(2*d-1)*h.1*h.2 : ℕ) : ℤ) := by
  unfold phasePolynomial
  simp only [finset_sum_coeff]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · rw [show exponent d 0 0=2*d-2 by unfold exponent; omega,
        coeff_monomial,if_pos rfl,coefficient_zero_zero]
    · intro j hj hj0
      rw [coeff_monomial,if_neg]
      unfold exponent
      omega
    · intro hbad
      exact False.elim (hbad (Finset.mem_range.mpr (by omega)))
  · intro i hi hi0
    apply Finset.sum_eq_zero
    intro j hj
    rw [coeff_monomial,if_neg]
    unfold exponent
    omega
  · intro hbad
    exact False.elim (hbad (Finset.mem_range.mpr (by omega)))

theorem phasePolynomial_natDegree {d : ℕ} {h m : Pair} (hd : 2 ≤ d)
    (hh : 0 < h.1) (ha : 0 < h.2) :
    (phasePolynomial d h m).natDegree=2*d-2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (phasePolynomial_natDegree_le d h m)
  rw [phasePolynomial_coeff_top hd]
  have hk : 0 < 2*d-1 := by omega
  positivity

theorem realPolynomial_natDegree {d : ℕ} {h m : Pair} (hd : 2 ≤ d)
    (hh : 0 < h.1) (ha : 0 < h.2) :
    (realPolynomial d h m).natDegree=2*d-2 := by
  rw [realPolynomial,natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),
    phasePolynomial_natDegree hd hh ha]

theorem realPolynomial_leadingCoeff {d : ℕ} {h m : Pair} (hd : 2 ≤ d)
    (hh : 0 < h.1) (ha : 0 < h.2) :
    (realPolynomial d h m).leadingCoeff=((4*(2*d)*(2*d-1)*h.1*h.2 : ℕ) : ℝ) := by
  rw [realPolynomial,leadingCoeff_map' (Int.cast_injective (α := ℝ)),
    leadingCoeff,phasePolynomial_natDegree hd hh ha,phasePolynomial_coeff_top hd]
  rfl

def middleCoefficient (d : ℕ) : ℕ := 4*(2*d).choose 3*(2*d-3)
def lowCoefficient (d : ℕ) : ℕ := 4*(2*d).choose 5*(2*d-5)/3

set_option maxHeartbeats 800000 in
theorem phasePolynomial_coeff_middle {d : ℕ} (hd : supportedHalfDegree d) (h m : Pair) :
    (phasePolynomial d h m).coeff (2*d-4)=
      (h.1*h.2*middleCoefficient d*((amplitude d h m).1^2+(amplitude d h m).2^2) : ℕ) := by
  simp only [phasePolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  rcases hd with rfl | rfl | rfl <;>
    norm_num [exponent,Finset.sum_range_succ] <;>
    norm_num [coefficient,Nat.choose,amplitude,middleCoefficient] <;> ring

set_option maxHeartbeats 800000 in
theorem phasePolynomial_coeff_low {d : ℕ} (hd : supportedHalfDegree d) (h m : Pair) :
    (phasePolynomial d h m).coeff (2*d-6)=
      (h.1*h.2*lowCoefficient d*(3*((amplitude d h m).1^4+(amplitude d h m).2^4)+
        10*(amplitude d h m).1^2*(amplitude d h m).2^2) : ℕ) := by
  simp only [phasePolynomial,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  rcases hd with rfl | rfl | rfl <;>
    norm_num [exponent,Finset.sum_range_succ] <;>
    norm_num [coefficient,Nat.choose,amplitude,lowCoefficient] <;> ring

theorem amplitude_eq_or_swap {d : ℕ} (hd : supportedHalfDegree d) {h m n : Pair}
    (h₁ : 0 < h.1) (h₂ : 0 < h.2)
    (he : phasePolynomial d h m=phasePolynomial d h n) :
    amplitude d h m=amplitude d h n ∨
      amplitude d h m=((amplitude d h n).2,(amplitude d h n).1) := by
  have hcM := congrArg (fun p : Polynomial ℤ => p.coeff (2*d-4)) he
  dsimp only at hcM
  rw [phasePolynomial_coeff_middle hd,phasePolynomial_coeff_middle hd] at hcM
  have hM : h.1*h.2*middleCoefficient d*((amplitude d h m).1^2+(amplitude d h m).2^2) =
      h.1*h.2*middleCoefficient d*((amplitude d h n).1^2+(amplitude d h n).2^2) := by
    exact_mod_cast hcM
  have hmid : 0 < middleCoefficient d := by
    rcases hd with rfl | rfl | rfl <;> norm_num [middleCoefficient,Nat.choose]
  have hlow : 0 < lowCoefficient d := by
    rcases hd with rfl | rfl | rfl <;> norm_num [lowCoefficient,Nat.choose]
  have hs := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < h.1*h.2*middleCoefficient d) hM
  have hcL := congrArg (fun p : Polynomial ℤ => p.coeff (2*d-6)) he
  dsimp only at hcL
  rw [phasePolynomial_coeff_low hd,phasePolynomial_coeff_low hd] at hcL
  have hL : h.1*h.2*lowCoefficient d*(3*((amplitude d h m).1^4+(amplitude d h m).2^4)+
      10*(amplitude d h m).1^2*(amplitude d h m).2^2) =
      h.1*h.2*lowCoefficient d*(3*((amplitude d h n).1^4+(amplitude d h n).2^4)+
      10*(amplitude d h n).1^2*(amplitude d h n).2^2) := by exact_mod_cast hcL
  have hL' := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < h.1*h.2*lowCoefficient d) hL
  have hprod : (amplitude d h m).1^2*(amplitude d h m).2^2 =
      (amplitude d h n).1^2*(amplitude d h n).2^2 := by
    nlinarith [congrArg (fun t : ℕ => t^2) hs]
  rcases SeedCompletionNinthDouble.pair_eq_or_swap_of_sum_prod hs hprod with hp | hp
  · exact Or.inl (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.2))
  · exact Or.inr (Prod.ext
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.1)
      (Nat.pow_left_injective (by norm_num : 2 ≠ 0) hp.2))

theorem amplitude_injective {d : ℕ} (hd : 0 < d) {h : Pair}
    (h₁ : 0 < h.1) (h₂ : 0 < h.2) : Function.Injective (amplitude d h) := by
  intro m n he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  change h.1*m.1^(2*d)=h.1*n.1^(2*d) at h1
  change h.2*m.2^(2*d)=h.2*n.2^(2*d) at h2
  exact Prod.ext
    (Nat.pow_left_injective (by omega : 2*d ≠ 0) (Nat.eq_of_mul_eq_mul_left h₁ h1))
    (Nat.pow_left_injective (by omega : 2*d ≠ 0) (Nat.eq_of_mul_eq_mul_left h₂ h2))

theorem polynomial_fiber_card_le_two {d : ℕ} (hd : supportedHalfDegree d)
    (h m : Pair) (B : Finset Pair) (h₁ : 0 < h.1) (h₂ : 0 < h.2) :
    (B.filter (fun n => phasePolynomial d h n=phasePolynomial d h m)).card ≤ 2 := by
  classical
  have hd0 : 0 < d := by rcases hd with rfl | rfl | rfl <;> omega
  let F := B.filter (fun n => phasePolynomial d h n=phasePolynomial d h m)
  have hs : F.image (amplitude d h) ⊆
      {amplitude d h m,((amplitude d h m).2,(amplitude d h m).1)} := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    rcases amplitude_eq_or_swap hd h₁ h₂ (Finset.mem_filter.mp hn).2 with he | he
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  calc
    _ = (F.image (amplitude d h)).card := by
      symm
      exact Finset.card_image_iff.mpr (amplitude_injective hd0 h₁ h₂).injOn
    _ ≤ ({amplitude d h m,((amplitude d h m).2,(amplitude d h m).1)} : Finset Pair).card :=
      Finset.card_le_card hs
    _ ≤ 2 := Finset.card_le_two

#print axioms phase_center_strictMono
#print axioms phasePolynomial_coeff_middle
#print axioms phasePolynomial_coeff_low
#print axioms polynomial_fiber_card_le_two
end Waring.SeedCompletionEvenDouble
