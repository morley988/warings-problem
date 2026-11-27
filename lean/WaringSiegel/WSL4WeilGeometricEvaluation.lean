import WaringSiegel.WSL4WeilGeometricIdentity

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1500000

/-- The cleared inverse Vandermonde identity evaluated in any commutative ring. -/
theorem exists_geometric_integral_power_identity_eval
    {R : Type*} [CommRing R] (n sigma : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤n) :
    ∃ u : Fin (n+1) → ℕ, ∃ Q : Fin (n+1) → ℤ[X],
      (∀j,u j+j.val*(j.val-1)/2+(n-j.val)*j.val=
        n*sigma+(n-sigma)*(n-sigma-1)/2 ∧
        (Q j).natDegree≤(sigma+1)*(n-sigma)+(sigma-1)*(n*(n+1)/2)+j.val*(n-j.val)) ∧
      ∀ y x : R,
      (∑ j,y^(u j)*(Q j).eval₂ (Int.castRingHom R) y*(y^j.val*x+1)^n)=
        (n.choose sigma:R)*(y^n*(WSL4Local.qFactorial n).eval₂ (Int.castRingHom R) y)^sigma*x^sigma := by
  obtain ⟨u,Q,hdegree,hidentity⟩ := exists_geometric_integral_power_identity n sigma hpos hsigma
  refine ⟨u,Q,hdegree,?_⟩
  intro y x
  have hh := congrArg
    (fun f : (ℤ[X])[X] => f.eval₂ (eval₂RingHom (Int.castRingHom R) y) x) hidentity
  simpa only [eval₂_finset_sum,eval₂_mul,eval₂_C,eval₂_pow,eval₂_add,eval₂_X,
    eval₂_one,eval₂_natCast,coe_eval₂RingHom] using hh

def geometricRamanujamScale {R : Type*} [CommRing R] (pi : R) (m n : ℕ) : R :=
  pi*((pi^m)^n*(WSL4Local.qFactorial n).eval₂ (Int.castRingHom R) (pi^m))

/-- Substituting `pi*x` makes every affine factor a principal unit. The coefficient
monomials remain literal m-th powers, independently of ramification. -/
theorem exists_geometric_uniformizer_power_identity
    {R : Type*} [CommRing R] (pi : R) (m n sigma : ℕ)
    (hpos : 1≤sigma) (hsigma : sigma≤n) :
    ∃ u : Fin (n+1) → ℕ, ∃ Q : Fin (n+1) → ℤ[X],
      (∀j,u j+j.val*(j.val-1)/2+(n-j.val)*j.val=
        n*sigma+(n-sigma)*(n-sigma-1)/2 ∧
        (Q j).natDegree≤(sigma+1)*(n-sigma)+(sigma-1)*(n*(n+1)/2)+j.val*(n-j.val)) ∧
      ∀ x : R,
      (∑ j,(pi^(u j))^m*(Q j).eval₂ (Int.castRingHom R) (pi^m)*
        (pi^(m*j.val+1)*x+1)^n)=
        (n.choose sigma:R)*(geometricRamanujamScale pi m n)^sigma*x^sigma := by
  obtain ⟨u,Q,hdegree,hidentity⟩ := exists_geometric_integral_power_identity_eval
    (R:=R) n sigma hpos hsigma
  refine ⟨u,Q,hdegree,?_⟩
  intro x
  have hh := hidentity (pi^m) (pi*x)
  have hterm (j : Fin (n+1)) :
      (pi^m)^(u j)*(Q j).eval₂ (Int.castRingHom R) (pi^m)*
        ((pi^m)^j.val*(pi*x)+1)^n=
      (pi^(u j))^m*(Q j).eval₂ (Int.castRingHom R) (pi^m)*
        (pi^(m*j.val+1)*x+1)^n := by
    have hpow : (pi^m)^(u j)=(pi^(u j))^m := by
      rw [← pow_mul,← pow_mul,Nat.mul_comm]
    rw [hpow,← pow_mul,pow_add,pow_one]
    ring
  simp_rw [hterm] at hh
  simpa only [geometricRamanujamScale,mul_pow,mul_assoc,mul_left_comm,mul_comm] using hh
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_geometric_integral_power_identity_eval
#print axioms WaringSiegel.WSL4Weil.exists_geometric_uniformizer_power_identity
