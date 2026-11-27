import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Integral Gaussian-binomial quotients for geometric interpolation

We construct the quotient by its polynomial recurrence. No division in
the coefficient ring and no integrality premise is used.
-/
noncomputable section
open Polynomial
open scoped BigOperators
namespace WaringSiegel.WSL4Local

def qFactorial (n : ℕ) : ℤ[X] := ∏ i∈Finset.range n,(1-X^(i+1))

@[simp] theorem qFactorial_zero : qFactorial 0=1 := by simp [qFactorial]

theorem qFactorial_succ (n : ℕ) :
    qFactorial (n+1)=qFactorial n*(1-X^(n+1)) := by
  simp only [qFactorial,Finset.prod_range_succ]

def gaussianBinomial : ℕ → ℕ → ℤ[X]
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 1
  | n+1,k+1 => gaussianBinomial n k+X^(k+1)*gaussianBinomial n (k+1)

@[simp] theorem gaussianBinomial_zero (n : ℕ) : gaussianBinomial n 0=1 := by
  cases n <;> rfl

theorem gaussianBinomial_eq_zero (n k : ℕ) (h : n<k) : gaussianBinomial n k=0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [gaussianBinomial]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp only [gaussianBinomial,ih k (by omega),ih (k+1) (by omega),mul_zero,add_zero]

@[simp] theorem gaussianBinomial_self (n : ℕ) : gaussianBinomial n n=1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gaussianBinomial,ih,gaussianBinomial_eq_zero n (n+1) (by omega),mul_zero,add_zero]

theorem qFactorial_mul_gaussianBinomial (n k : ℕ) (hk : k≤n) :
    qFactorial k*qFactorial (n-k)*gaussianBinomial n k=qFactorial n := by
  induction n generalizing k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases hkn : k=n
      · subst k
        simp
      have hk' : k+1≤n := by omega
      have hfac : qFactorial (n-k)=qFactorial (n-(k+1))*(1-X^(n-k)) := by
        have he : n-k=(n-(k+1))+1 := by omega
        conv_lhs => rw [he,qFactorial_succ]
        rw [← he]
      have hpow : (X:ℤ[X])^(k+1)*X^(n-k)=X^(n+1) := by
        rw [← pow_add]
        congr 1
        omega
      simp only [Nat.succ_sub_succ_eq_sub,gaussianBinomial]
      calc
        qFactorial (k+1)*qFactorial (n-k)*
            (gaussianBinomial n k+X^(k+1)*gaussianBinomial n (k+1))=
          (1-X^(k+1))*(qFactorial k*qFactorial (n-k)*gaussianBinomial n k)+
            X^(k+1)*(1-X^(n-k))*
              (qFactorial (k+1)*qFactorial (n-(k+1))*gaussianBinomial n (k+1)) := by
                rw [qFactorial_succ,hfac]
                ring
        _=(1-X^(k+1)+X^(k+1)-X^(k+1)*X^(n-k))*qFactorial n := by
          rw [ih k (by omega),ih (k+1) hk']
          ring
        _=qFactorial (n+1) := by rw [hpow,qFactorial_succ]; ring

theorem qFactorial_mul_dvd (n k : ℕ) (hk : k≤n) :
    qFactorial k*qFactorial (n-k)∣qFactorial n :=
  ⟨gaussianBinomial n k,(qFactorial_mul_gaussianBinomial n k hk).symm⟩

theorem gaussianBinomial_natDegree_le (n k : ℕ) :
    (gaussianBinomial n k).natDegree≤k*(n-k) := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussianBinomial]
  | succ n ih =>
    by_cases hkn : n+1<k
    · rw [gaussianBinomial_eq_zero _ _ hkn]
      simp
    cases k with
    | zero => simp
    | succ k =>
      by_cases hkn' : k=n
      · subst k
        simp
      have hk : k+1≤n := by omega
      have hd1 := ih k
      have hd2 := ih (k+1)
      have hm := Polynomial.natDegree_mul_le (p:=(X^(k+1):ℤ[X])) (q:=gaussianBinomial n (k+1))
      rw [Polynomial.natDegree_X_pow] at hm
      rw [gaussianBinomial]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · exact hd1.trans (by simp only [Nat.succ_sub_succ_eq_sub]; nlinarith)
      · have he : n-k=n-(k+1)+1 := by omega
        simp only [Nat.succ_sub_succ_eq_sub]
        nlinarith

#print axioms qFactorial_mul_dvd
#print axioms gaussianBinomial_natDegree_le
end WaringSiegel.WSL4Local
