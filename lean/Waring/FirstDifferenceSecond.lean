import Waring.IntegerDifferencePolynomial
import Waring.AuxiliaryL2Grouping
import Mathlib.Data.Nat.Choose.Basic

/-!
# First centered-difference second moments in the even degrees

For positive height and center the normalized first difference in an even
degree has positive integer coefficients. Its value is divisible by both
the height and center, and strictly increases in the positive coefficient.
Thus a nonzero frequency has at most a squared divisor count of preimages.
This supplies the actual sharp auxiliary second-moment input, rather than
assuming a first-difference mean-value theorem.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FirstDifferenceSecond
open IntegerDifferencePolynomial AuxiliaryL2Grouping

/-- The positive-coefficient expansion for degree `2*d`. -/
def evenPhase (d h m z : ℕ) : ℕ :=
  ∑ i ∈ Finset.range d,
    2 * (2*d).choose (2*i+1) * h^(2*i+1) * z^(2*d-(2*i+1)) * m^((2*d)*(2*i))

theorem height_dvd_evenPhase (d h m z : ℕ) : h ∣ evenPhase d h m z := by
  unfold evenPhase
  apply Finset.dvd_sum
  intro i hi
  refine ⟨2 * (2*d).choose (2*i+1) * h^(2*i) * z^(2*d-(2*i+1)) * m^((2*d)*(2*i)),?_⟩
  rw [pow_succ]
  ring

theorem center_dvd_evenPhase (d h m z : ℕ) : z ∣ evenPhase d h m z := by
  unfold evenPhase
  apply Finset.dvd_sum
  intro i hi
  have hi' : i < d := Finset.mem_range.mp hi
  have hexp : 2*d-(2*i+1) = (2*d-(2*i+1)-1)+1 := by omega
  refine ⟨2 * (2*d).choose (2*i+1) * h^(2*i+1) * z^(2*d-(2*i+1)-1) * m^((2*d)*(2*i)),?_⟩
  conv_lhs => rw [hexp]
  rw [pow_succ z]
  ring

theorem evenPhase_pos {d h m z : ℕ} (hd : 0 < d) (hh : 0 < h) (hz : 0 < z) :
    0 < evenPhase d h m z := by
  unfold evenPhase
  apply Finset.sum_pos'
  · intro i hi
    exact Nat.zero_le _
  · refine ⟨0,Finset.mem_range.mpr hd,?_⟩
    simp only [mul_zero,zero_add,pow_zero,mul_one,pow_one,Nat.choose_one_right]
    positivity

theorem evenPhase_strictMono {d h z : ℕ} (hd : 2 ≤ d) (hh : 0 < h) (hz : 0 < z) :
    StrictMono (fun m => evenPhase d h m z) := by
  intro m n hmn
  unfold evenPhase
  apply Finset.sum_lt_sum
  · intro i hi
    gcongr
  · refine ⟨1,Finset.mem_range.mpr (by omega),?_⟩
    have hc : 0 < (2*d).choose (2*1+1) := Nat.choose_pos (by omega)
    have hcoef : 0 < 2*(2*d).choose (2*1+1)*h^(2*1+1)*z^(2*d-(2*1+1)) := by positivity
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left hmn (by omega)) hcoef

/-- The three even degrees needed by the target and coefficient seed curves. -/
def supportedHalfDegree (d : ℕ) : Prop := d = 4 ∨ d = 8 ∨ d = 9

theorem evenPhase_mul_identity {d : ℕ} (hd : supportedHalfDegree d) (h m z : ℕ) :
    (m : ℤ)^(2*d) * (evenPhase d h m z : ℤ) =
      ((z : ℤ)+(h : ℤ)*(m : ℤ)^(2*d))^(2*d) -
      ((z : ℤ)-(h : ℤ)*(m : ℤ)^(2*d))^(2*d) := by
  rcases hd with rfl | rfl | rfl <;>
    norm_num [evenPhase,Finset.sum_range_succ,Nat.choose] <;> ring

/-- The expansion is the actual integral-frequency polynomial already used
by the fundamental recurrence. -/
theorem evenPhase_eq_powerPolynomial {d : ℕ} (hd : supportedHalfDegree d)
    (h m z : ℕ) (hm : 0 < m) :
    (evenPhase d h m z : ℤ) =
      (powerPolynomial (2*d) [((h : ℤ),(m : ℤ))]).eval (z : ℤ) := by
  have hm0 : (m : ℤ)^(2*d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm.ne')
  apply mul_left_cancel₀ hm0
  rw [evenPhase_mul_identity hd]
  have H := congrArg (fun p : Polynomial ℤ => p.eval (z : ℤ))
    (difference_mul (2*d) (h : ℤ) (m : ℤ) (Polynomial.X^(2*d)))
  simpa only [powerPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_sub,Polynomial.eval_comp,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X] using H.symm

#print axioms evenPhase_strictMono
#print axioms evenPhase_eq_powerPolynomial
end Waring.FirstDifferenceSecond
