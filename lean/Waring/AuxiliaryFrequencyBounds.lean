import Waring.AuxiliaryL2Counting
import Mathlib.Tactic.GCongr

/-!
# Polynomial frequency ranges for the literal degree-eight quadratic sum

The coarse exponents are deliberately generous. Their role is only to make
the divisor bound uniform. The optimized auxiliary exponent is supplied by
the exact coefficient zero count, not by these ambient bounds.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryFrequencyBounds
open Waring.AuxiliaryL2Counting

theorem coefficientValue_nonneg {r : ℕ} (k : ℕ) (h m : Fin r → ℕ) :
    0 ≤ coefficientValue k h m := by
  exact Finset.sum_nonneg (fun i hi => by positivity)

theorem coefficientValue_pos (h m : Fin 6 → ℕ)
    (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i) :
    0 < coefficientValue 16 h m := by
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · refine ⟨0,Finset.mem_univ _,?_⟩
    have hh0 : (0:ℤ)<h 0 := by exact_mod_cast hh 0
    have hm0 : (0:ℤ)<m 0 := by exact_mod_cast hm 0
    positivity

theorem frequency_pos (h m : Fin 6 → ℕ) (z : ℤ)
    (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i) :
    0 < frequency 430080 16 (h,(m,z)) := by
  have hprod : 0 < shiftProduct h := Finset.prod_pos (fun i hi => by exact_mod_cast hh i)
  have hcoef := coefficientValue_pos h m hh hm
  unfold frequency
  dsimp only
  have hz := sq_nonneg z
  positivity

theorem shift_dvd_frequency {r : ℕ} (C : ℤ) (k : ℕ)
    (h m : Fin r → ℕ) (z : ℤ) (i : Fin r) :
    (h i:ℤ) ∣ frequency C k (h,(m,z)) := by
  have hp : (h i:ℤ) ∣ shiftProduct h := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp C) _

theorem coefficientValue_real_le {P : ℝ} (hP : 1 ≤ P) (h m : Fin 6 → ℕ)
    (hh : ∀ i, (h i:ℝ) ≤ P) (hm : ∀ i, (m i:ℝ) ≤ P) :
    (coefficientValue 16 h m:ℝ) ≤ 6*P^18 := by
  have hP0 := zero_le_one.trans hP
  have hterm (i : Fin 6) : (h i:ℝ)^2*(m i:ℝ)^16 ≤ P^18 := by
    calc
      _ ≤ P^2*P^16 := mul_le_mul
        (pow_le_pow_left₀ (by positivity) (hh i) 2)
        (pow_le_pow_left₀ (by positivity) (hm i) 16) (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]
  calc
    _ = ∑ i : Fin 6, (h i:ℝ)^2*(m i:ℝ)^16 := by simp [coefficientValue]
    _ ≤ ∑ i : Fin 6, P^18 := Finset.sum_le_sum (fun i hi => hterm i)
    _ = _ := by simp

theorem shiftProduct_real_le {P : ℝ} (hP : 0 ≤ P) (h : Fin 6 → ℕ)
    (hh : ∀ i, (h i:ℝ) ≤ P) : (shiftProduct h:ℝ) ≤ P^6 := by
  calc
    _ = ∏ i : Fin 6, (h i:ℝ) := by simp [shiftProduct]
    _ ≤ ∏ i : Fin 6, P := Finset.prod_le_prod (fun i hi => by positivity) (fun i hi => hh i)
    _ = _ := by simp

theorem frequency_natAbs_le {P : ℝ} (hP : 3870720 ≤ P)
    (h m : Fin 6 → ℕ) (z : ℤ)
    (hhpos : ∀ i, 0 < h i) (hmpos : ∀ i, 0 < m i)
    (hh : ∀ i, (h i:ℝ) ≤ P) (hm : ∀ i, (m i:ℝ) ≤ P)
    (hz : |(z:ℝ)| ≤ P) :
    ((frequency 430080 16 (h,(m,z))).natAbs:ℝ) ≤ P^25 := by
  have hP1 : 1 ≤ P := by linarith
  have hP0 := zero_le_one.trans hP1
  have hfpos := frequency_pos h m z hhpos hmpos
  have hcoef := coefficientValue_real_le hP1 h m hh hm
  have hprod := shiftProduct_real_le hP0 h hh
  have hz2 : (z:ℝ)^2 ≤ P^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (z:ℝ)) hz 2
  have hP218 : P^2 ≤ P^18 := pow_le_pow_right₀ hP1 (by omega)
  have hterm : 3*(z:ℝ)^2+(coefficientValue 16 h m:ℝ) ≤ 9*P^18 := by linarith
  have hn : 0 ≤ 3*(z:ℝ)^2+(coefficientValue 16 h m:ℝ) := by
    have hc : (0:ℝ)≤(coefficientValue 16 h m:ℝ) := by exact_mod_cast coefficientValue_nonneg 16 h m
    positivity
  have hcast : ((frequency 430080 16 (h,(m,z))).natAbs:ℝ) =
      (frequency 430080 16 (h,(m,z)):ℝ) := by
    have hh : (((frequency 430080 16 (h,(m,z))).natAbs:ℕ):ℤ) =
        frequency 430080 16 (h,(m,z)) := by
      rw [Int.natCast_natAbs,abs_of_nonneg hfpos.le]
    have hhR := congrArg (fun z : ℤ => (z:ℝ)) hh
    simpa only [Int.cast_natCast] using hhR
  rw [hcast]
  calc
    _ = 430080*(shiftProduct h:ℝ)*(3*(z:ℝ)^2+(coefficientValue 16 h m:ℝ)) := by simp [frequency]
    _ ≤ 430080*(P^6)*(9*P^18) := by gcongr
    _ = 3870720*P^24 := by ring
    _ ≤ P*P^24 := mul_le_mul_of_nonneg_right hP (by positivity)
    _ = P^25 := by ring

theorem coefficient_difference_natAbs_le {P : ℝ} (hP : 6 ≤ P)
    (h m n : Fin 6 → ℕ)
    (hh : ∀ i, (h i:ℝ) ≤ P) (hm : ∀ i, (m i:ℝ) ≤ P) (hn : ∀ i, (n i:ℝ) ≤ P) :
    ((coefficientValue 16 h m-coefficientValue 16 h n).natAbs:ℝ) ≤ P^20 := by
  have hP1 : 1 ≤ P := by linarith
  have hP0 := zero_le_one.trans hP1
  have hmlo : (0:ℝ)≤(coefficientValue 16 h m:ℝ) := by exact_mod_cast coefficientValue_nonneg 16 h m
  have hnlo : (0:ℝ)≤(coefficientValue 16 h n:ℝ) := by exact_mod_cast coefficientValue_nonneg 16 h n
  have hmhi := coefficientValue_real_le hP1 h m hh hm
  have hnhi := coefficientValue_real_le hP1 h n hh hn
  have habs : |(coefficientValue 16 h m:ℝ)-(coefficientValue 16 h n:ℝ)| ≤ 6*P^18 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hcast : ((coefficientValue 16 h m-coefficientValue 16 h n).natAbs:ℝ) =
      |(coefficientValue 16 h m:ℝ)-(coefficientValue 16 h n:ℝ)| := by
    have hhR := congrArg (fun z : ℤ => (z:ℝ))
      (Int.natCast_natAbs (coefficientValue 16 h m-coefficientValue 16 h n))
    simpa only [Int.cast_natCast,Int.cast_abs,Int.cast_sub] using hhR
  rw [hcast]
  calc
    _ ≤ 6*P^18 := habs
    _ ≤ P^2*P^18 := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = P^20 := by ring

#print axioms frequency_natAbs_le
#print axioms coefficient_difference_natAbs_le

end Waring.AuxiliaryFrequencyBounds
