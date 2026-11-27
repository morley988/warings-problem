import WaringSiegel.WSL4WeilGeometricPowers

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1500000

/-- Two neighboring integer-square parities give the sharp common bound for
both variable terms in the interpolation coefficient degree. -/
theorem geometric_quadratic_integer_bound (P s j : ℤ) :
    2*((s+1)*(P-s)+j*(P-j))≤P*(P+1) := by
  have h2 : 0≤(P-2*j)^2 := sq_nonneg _
  by_cases h : P-2*s-1=0
  · have hj : P-2*j≠0 := by omega
    have hjpos : 0<(P-2*j)^2 := sq_pos_of_ne_zero hj
    nlinarith
  · have hpos : 0<(P-2*s-1)^2 := sq_pos_of_ne_zero h
    nlinarith

theorem geometric_degree_bound_uniform
    (P sigma j : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤P) (hj : j≤P) :
    (sigma+1)*(P-sigma)+(sigma-1)*(P*(P+1)/2)+j*(P-j)
      ≤sigma*(P*(P+1)/2) := by
  have hi : 2*((sigma+1)*(P-sigma)+j*(P-j))≤P*(P+1) := by
    zify [hsigma,hj]
    exact geometric_quadratic_integer_bound P sigma j
  have half : (sigma+1)*(P-sigma)+j*(P-j)≤P*(P+1)/2 := by omega
  calc
    _ = ((sigma+1)*(P-sigma)+j*(P-j))+(sigma-1)*(P*(P+1)/2) := by omega
    _ ≤ P*(P+1)/2+(sigma-1)*(P*(P+1)/2) := Nat.add_le_add_right half _
    _ = sigma*(P*(P+1)/2) := by
      rw [Nat.add_comm,← Nat.succ_mul,Nat.succ_eq_add_one,Nat.sub_add_cancel hpos]

theorem geometric_polynomial_degree_sum_bound
    {R : Type*} [Semiring R] (P sigma : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤P)
    (Q : Fin (P+1) → R[X])
    (hdegree : ∀j,(Q j).natDegree≤
      (sigma+1)*(P-sigma)+(sigma-1)*(P*(P+1)/2)+j.val*(P-j.val)) :
    (∑j,((Q j).natDegree+1))≤(P+1)*(sigma*(P*(P+1)/2)+1) := by
  calc
    _ ≤ ∑ _j : Fin (P+1),(sigma*(P*(P+1)/2)+1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.add_le_add_right ((hdegree j).trans
        (geometric_degree_bound_uniform P sigma j.val hpos hsigma (by omega))) 1
    _ = _ := by simp

theorem geometric_polynomial_degree_sum_coarse_bound
    {R : Type*} [Semiring R] (P sigma : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤P)
    (Q : Fin (P+1) → R[X])
    (hdegree : ∀j,(Q j).natDegree≤
      (sigma+1)*(P-sigma)+(sigma-1)*(P*(P+1)/2)+j.val*(P-j.val)) :
    (∑j,((Q j).natDegree+1))≤(P+1)*(P*(P+1)/2+1)*sigma := by
  have hh := geometric_polynomial_degree_sum_bound P sigma hpos hsigma Q hdegree
  have he : sigma*(P*(P+1)/2)+1≤(P*(P+1)/2+1)*sigma := by nlinarith
  exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (P+1) he)
theorem geometric_degree_budget_sum_bound
    (P sigma : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤P) :
    (∑j : Fin (P+1),((sigma+1)*(P-sigma)+(sigma-1)*(P*(P+1)/2)+
      j.val*(P-j.val)+1))≤sigma*(P+1)*(P*(P+1)/2+1) := by
  calc
    _ ≤ ∑_j : Fin (P+1),(sigma*(P*(P+1)/2)+1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.add_le_add_right
        (geometric_degree_bound_uniform P sigma j.val hpos hsigma (by omega)) 1
    _ = (P+1)*(sigma*(P*(P+1)/2)+1) := by simp
    _ ≤ sigma*(P+1)*(P*(P+1)/2+1) := by nlinarith

end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.geometric_degree_bound_uniform
#print axioms WaringSiegel.WSL4Weil.geometric_polynomial_degree_sum_bound
#print axioms WaringSiegel.WSL4Weil.geometric_polynomial_degree_sum_coarse_bound

#print axioms WaringSiegel.WSL4Weil.geometric_degree_budget_sum_bound
