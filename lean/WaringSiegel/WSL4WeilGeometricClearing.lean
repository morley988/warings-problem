import WaringSiegel.WSL4WeilGeometricNumerator
import WaringSiegel.WSL4WeilGeometricDenominator

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

theorem triangle_add_exact (a b : ℕ) :
    (a+b)*(a+b-1)/2=a*(a-1)/2+b*(b-1)/2+a*b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a+(b+1)=(a+b)+1 by omega,Nat.triangle_succ,ih,Nat.triangle_succ]
    ring

theorem geometric_denominator_exponent_le (n sigma : ℕ) (j : Fin (n+1))
    (hsigma : sigma≤n) :
    j.val*(j.val-1)/2+(n-j.val)*j.val ≤ n*sigma+(n-sigma)*(n-sigma-1)/2 := by
  have hj : j.val≤n := by omega
  have hd := triangle_add_exact j.val (n-j.val)
  rw [Nat.add_sub_of_le hj] at hd
  have hs := triangle_add_exact sigma (n-sigma)
  rw [Nat.add_sub_of_le hsigma] at hs
  have hb : sigma*(sigma-1)/2≤sigma*sigma := by
    calc _ ≤ sigma*(sigma-1) := Nat.div_le_self _ _
         _ ≤ sigma*sigma := Nat.mul_le_mul_left sigma (Nat.sub_le _ _)
  have he : sigma+(n-sigma)=n := Nat.add_sub_of_le hsigma
  calc
    _ ≤ j.val*(j.val-1)/2+(n-j.val)*j.val+(n-j.val)*(n-j.val-1)/2 :=
      Nat.le_add_right _ _
    _ = n*(n-1)/2 := by rw [hd]; ring
    _ = sigma*(sigma-1)/2+(n-sigma)*(n-sigma-1)/2+sigma*(n-sigma) := hs
    _ ≤ sigma*sigma+(n-sigma)*(n-sigma-1)/2+sigma*(n-sigma) :=
      Nat.add_le_add_right (Nat.add_le_add_right hb _) _
    _ = (sigma+(n-sigma))*sigma+(n-sigma)*(n-sigma-1)/2 := by ring
    _ = _ := by rw [he]

theorem qFactorial_natDegree_le (n : ℕ) :
    (WSL4Local.qFactorial n).natDegree≤n*(n+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : (1-(X:ℤ[X])^(n+1)).natDegree≤n+1 := by
      exact (natDegree_sub_le _ _).trans (by simp)
    have hm := natDegree_mul_le (p:=WSL4Local.qFactorial n) (q:=1-X^(n+1))
    rw [WSL4Local.qFactorial_succ]
    have htri := Nat.triangle_succ (n+1)
    have hntri : (n+1)*(n+1-1)/2=n*(n+1)/2 := by
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm]
    rw [hntri] at htri
    have he : (n+1+1)*(n+1+1-1)/2=(n+1)*(n+1+1)/2 := by
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_comm]
    rw [he] at htri
    omega

/-- Explicit integral clearing of one inverse row. The residual polynomial degree
retains the bound needed to count powers; its initial monomial is separated. -/
theorem geometric_inverse_row_integral_polynomial
    (n : ℕ) (j : Fin (n+1)) (sigma : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤n) :
    ∃ u : ℕ, ∃ Q : ℤ[X],
      u+j.val*(j.val-1)/2+(n-j.val)*j.val=
        n*sigma+(n-sigma)*(n-sigma-1)/2 ∧
      Q.natDegree≤(sigma+1)*(n-sigma)+(sigma-1)*(n*(n+1)/2)+j.val*(n-j.val) ∧
      (∏ i∈Finset.univ.erase j,((X:ℤ[X])^j.val-X^i.val))*(X^u*Q)=
        (X^n*WSL4Local.qFactorial n)^sigma*
          (∏ i∈Finset.univ.erase j,((X:(ℤ[X])[X])-C ((X:ℤ[X])^i.val))).coeff sigma := by
  obtain ⟨P,hP,hdeg⟩ := geometricNumerator_factor n j sigma hsigma
  let D := j.val*(j.val-1)/2+(n-j.val)*j.val
  let T := (n-sigma)*(n-sigma-1)/2
  let u := n*sigma+T-D
  let Q : ℤ[X] := (-1)^j.val*WSL4Local.qFactorial n^(sigma-1)*
    WSL4Local.gaussianBinomial n j.val*P
  have hu : u+D=n*sigma+T := Nat.sub_add_cancel
    (geometric_denominator_exponent_le n sigma j hsigma)
  have hQ : Q.natDegree≤(sigma+1)*(n-sigma)+(sigma-1)*(n*(n+1)/2)+j.val*(n-j.val) := by
    have h1 := natDegree_mul_le
      (p:=(-1 : ℤ[X])^j.val*WSL4Local.qFactorial n^(sigma-1)*WSL4Local.gaussianBinomial n j.val)
      (q:=P)
    have h2 := natDegree_mul_le
      (p:=(-1 : ℤ[X])^j.val*WSL4Local.qFactorial n^(sigma-1))
      (q:=WSL4Local.gaussianBinomial n j.val)
    have h3 := natDegree_mul_le
      (p:=(-1 : ℤ[X])^j.val) (q:=WSL4Local.qFactorial n^(sigma-1))
    have h4 := qFactorial_natDegree_le n
    have h5 := WSL4Local.gaussianBinomial_natDegree_le n j.val
    simp only [natDegree_pow,natDegree_neg,natDegree_one,mul_zero,zero_add] at h3
    have h6 := Nat.mul_le_mul_left (sigma-1) h4
    dsimp only [Q]
    omega
  refine ⟨u,Q,by simpa only [D,T,Nat.add_assoc] using hu,hQ,?_⟩
  rw [geometric_denominator_polynomial_factor,hP]
  change ((-1 : ℤ[X])^j.val*X^D*WSL4Local.qFactorial j.val*
      WSL4Local.qFactorial (n-j.val))*(X^u*Q)=
      (X^n*WSL4Local.qFactorial n)^sigma*(X^T*P)
  have hsign : (-1 : ℤ[X])^j.val*(-1)^j.val=1 := by
    rw [← mul_pow]
    norm_num
  have hgauss := WSL4Local.qFactorial_mul_gaussianBinomial n j.val (by omega)
  calc
    _ = ((-1 : ℤ[X])^j.val*(-1)^j.val)*(X^u*X^D)*
        (WSL4Local.qFactorial j.val*WSL4Local.qFactorial (n-j.val)*
          WSL4Local.gaussianBinomial n j.val)*WSL4Local.qFactorial n^(sigma-1)*P := by
      dsimp [Q]
      ring
    _ = X^(n*sigma+T)*(WSL4Local.qFactorial n*WSL4Local.qFactorial n^(sigma-1))*P := by
      rw [hsign,one_mul,← pow_add,hu,hgauss]
      ring
    _ = _ := by
      rw [← pow_succ',Nat.sub_add_cancel hpos,pow_add,mul_pow,pow_mul]
      ring
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.geometric_inverse_row_integral_polynomial
