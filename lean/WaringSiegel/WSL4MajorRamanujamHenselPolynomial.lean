import WaringSiegel.WSL4ArchLocalAffine
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Div

/-! # Integral rescaled prime-power polynomials for sharp local lifting -/
noncomputable section
set_option maxHeartbeats 1400000
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4

theorem prime_scaled_binomial_dvd (p d i : ℕ) (hp : p.Prime) (hd : 1 ≤ d)
    (hdp : d+2 ≤ d*p) (hi : 2 ≤ i) :
    p^(d+2) ∣ p.choose i*(p^d)^i := by
  by_cases hip : i<p
  · have hb := hp.dvd_choose_self (by omega : i ≠ 0) hip
    have he : d+1 ≤ d*i := by nlinarith
    have hh : p^(d+1)∣(p^d)^i := by
      rw [← pow_mul]
      exact pow_dvd_pow p he
    have h := mul_dvd_mul hb hh
    simpa only [← pow_succ',Nat.add_assoc,show (1:ℕ)+1=2 from rfl] using h
  · by_cases hieq : i=p
    · subst i
      simp only [Nat.choose_self,one_mul,← pow_mul]
      exact pow_dvd_pow p hdp
    · rw [Nat.choose_eq_zero_of_lt (by omega),zero_mul]
      exact dvd_zero _

theorem exists_prime_scaled_lift_polynomial (p d : ℕ) (hp : p.Prime)
    (hd : 1 ≤ d) (hdp : d+2 ≤ d*p) :
    ∃ F : ℤ[X],
      (1+C ((p:ℤ)^d)*X)^p=1+C ((p:ℤ)^(d+1))*F ∧
      F.map (Int.castRingHom (ZMod p))=X := by
  let T : ℤ[X] := (1+C ((p:ℤ)^d)*X)^p-1-C ((p:ℤ)^(d+1))*X
  have hcoeff (i : ℕ) : ((1+C ((p:ℤ)^d)*X)^p).coeff i =
      (p.choose i:ℤ)*((p:ℤ)^d)^i := by
    have he : (1+C ((p:ℤ)^d)*X)^p = ((1+X)^p).comp (C ((p:ℤ)^d)*X) := by simp
    rw [he,comp_C_mul_X_coeff,coeff_one_add_X_pow]
  have hdiv : C ((p:ℤ)^(d+2)) ∣ T := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    dsimp only [T]
    rw [coeff_sub,coeff_sub,hcoeff,coeff_one,coeff_C_mul,coeff_X]
    by_cases hi0 : i = 0
    · subst i
      simp
    · by_cases hi1 : i = 1
      · subst i
        simp [pow_succ']
      · have hi : 2 ≤ i := by omega
        have hh := prime_scaled_binomial_dvd p d i hp hd hdp hi
        simpa only [if_neg hi0,if_neg (Ne.symm hi1),mul_zero,sub_zero] using
          (show (p:ℤ)^(d+2) ∣ (p.choose i:ℤ)*((p:ℤ)^d)^i by exact_mod_cast hh)
  obtain ⟨G,hG⟩ := hdiv
  let F : ℤ[X] := X+C (p:ℤ)*G
  refine ⟨F,?_,?_⟩
  · calc
      _ = 1+C ((p:ℤ)^(d+1))*X+T := by dsimp [T]; ring
      _ = 1+C ((p:ℤ)^(d+1))*X+C ((p:ℤ)^(d+2))*G := by rw [hG]
      _ = _ := by
        have he : C ((p:ℤ)^(d+2))=C ((p:ℤ)^(d+1))*C (p:ℤ) := by
          rw [show d+2=(d+1)+1 by omega,pow_succ,map_mul]
        rw [he]
        dsimp [F]
        ring
  · simp [F]

theorem exists_binomial_quadratic_tail (n : ℕ) :
    ∃ G : ℤ[X], (1+X)^n=1+C (n:ℤ)*X+X^2*G := by
  let T : ℤ[X] := (1+X)^n-1-C (n:ℤ)*X
  have hd : X^2∣T := by
    rw [X_pow_dvd_iff]
    intro i hi
    interval_cases i <;> simp only [T,coeff_sub,coeff_one_add_X_pow,coeff_one,
      coeff_C_mul,coeff_X,Nat.choose_zero_right,Nat.choose_one_right,Int.cast_one,
      if_pos rfl,one_ne_zero,zero_ne_one,if_false,mul_one,mul_zero,sub_self,sub_zero] <;> norm_num
  obtain ⟨G,hG⟩ := hd
  refine ⟨G,?_⟩
  have he : (1+X)^n-1-C (n:ℤ)*X=X^2*G := hG
  linear_combination he

#print axioms exists_prime_scaled_lift_polynomial
#print axioms exists_binomial_quadratic_tail
end WaringSiegel.WSL4
