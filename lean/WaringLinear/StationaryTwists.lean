import WaringLinear.EvenStationaryBranch
import WaringLinear.OddStationaryBranch

/-! # Fourier transforms of a polynomial on one nondegenerate residue class

The Hessian phase remains constant over the permitted dual residue class.
All other dual classes have exact cancellation. No factor counting possible
residue representatives enters these local identities.
-/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] [IsLocalRing A] [Fintype A]

def linearlyTwisted (f : A[X]) (b : A) := f-C b*X

theorem twisted_derivative (f : A[X]) (b : A) :
    (linearlyTwisted f b).derivative=f.derivative-C b := by simp [linearlyTwisted]

theorem twisted_hessian (f : A[X]) (b : A) :
    (linearlyTwisted f b).derivative.derivative=f.derivative.derivative := by
  rw [twisted_derivative];simp

theorem twisted_hasse (f : A[X]) (b : A) :
    hasseDeriv 2 (linearlyTwisted f b)=hasseDeriv 2 f := by
  have hz : hasseDeriv 2 (C b*X)=0 := hasseDeriv_eq_zero_of_lt_natDegree _ _ <|
    lt_of_le_of_lt (natDegree_C_mul_le b X) (by simp)
  simp [linearlyTwisted,map_sub,hz]

theorem odd_phase_constant (ψ : AddChar A ℂ) (d h h' : A)
    (kill : ∀ x : A, residue A x=0 → d^2*x=0) (eq : residue A h=residue A h') :
    oddGaussPhase ψ h d=oddGaussPhase ψ h' d := by
  have h₀ := kill (h-h') (by rw [map_sub,eq,sub_self])
  have h₁ : h*d^2=h'*d^2 := by linear_combination h₀
  simp only [oddGaussPhase,h₁]

/-- If the residual derivative misses a dual frequency, every stationary
term on this branch vanishes. -/
theorem nonstationary_branch_zero (ψ : AddChar A ℂ) (prim : ψ.IsPrimitive)
    (f : A[X]) (c y : A) (hc : c^2=0) (hne : c≠0) (hy : residue A (f.derivative.eval y)≠0) :
    (∑ x ∈ Finset.univ.filter (fun x : A => residue A x=residue A y), ψ (f.eval x))=0 := by
  have hres : residue A c=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp
    (by rw [←map_pow,hc,map_zero])
  let S := Finset.univ.filter (fun x : A => residue A x=residue A y)
  let w (x : A) : ℂ := if x∈S then 1 else 0
  have hS (x t : A) : x+c*t∈S ↔ x∈S := by simp [S,map_add,map_mul,hres]
  have filter := weighted_polynomial_stationary_filter ψ prim f c hc w (fun x t => by simp only [w,hS])
  change (∑ x∈S, ψ (f.eval x))=0
  calc
    _ = ∑ x : A, w x*ψ (f.eval x) := by
      simp only [w,ite_mul,one_mul,zero_mul,←Finset.sum_filter];simp
    _ = _ := filter
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hf := (Finset.mem_filter.mp hx).2
      have hnot : x∉S := by
        intro hmem
        have he := eval_same_residue f.derivative (Finset.mem_filter.mp hmem).2
        have hu := (residue_ne_zero_iff_isUnit _).1 (he ▸ hy)
        exact hne (hu.mul_left_inj.mp (hf.trans (zero_mul _).symm))
      simp [w,hnot]

/-- The same unit phase applies to every permissible linear Fourier
frequency on the chosen residue ball, including in ramified finite rings. -/
theorem odd_fourier_branch (ψ : AddChar A ℂ) (prim : ψ.IsPrimitive)
    (f : A[X]) (c d y b : A) (hc : c^2=0) (hd : d^3=0) (hne : c≠0)
    (hann : ∀ x : A, c*x=0 ↔ x∈Ideal.span {d})
    (hker : ∀ x : A, d*x=0 → x∈Ideal.span {d})
    (kill : ∀ x : A, residue A x=0 → d^2*x=0)
    (hder : IsUnit (f.derivative.derivative.eval y)) :
    let phase := oddGaussPhase ψ ((hasseDeriv 2 f).eval y) d
    let S := Finset.univ.filter (fun x : A => residue A x=residue A y)
    let sum := ∑ x∈S, ψ (f.eval x-b*x)
    (residue A b≠residue A (f.derivative.eval y) → sum=0) ∧
    (residue A b=residue A (f.derivative.eval y) →
      ∃ a, residue A a=residue A y ∧ f.derivative.eval a=b ∧ ‖phase‖=1 ∧
        sum=(Real.sqrt (Fintype.card A):ℂ)*ψ (f.eval a-b*a)*phase) := by
  let g := linearlyTwisted f b
  have hev (x : A) : g.eval x=f.eval x-b*x := by simp [g,linearlyTwisted]
  have hdv (x : A) : g.derivative.eval x=f.derivative.eval x-b := by
    simp [g,twisted_derivative]
  constructor
  · intro h
    have hmiss : residue A (g.derivative.eval y)≠0 := by rw [hdv,map_sub];exact sub_ne_zero.mpr (Ne.symm h)
    simpa only [hev] using nonstationary_branch_zero ψ prim g c y hc hne hmiss
  · intro h
    have hhit : residue A (g.derivative.eval y)=0 := by rw [hdv,map_sub,h,sub_self]
    obtain ⟨a,ha,hr,hn,hs⟩ := odd_stationary_branch ψ prim g c d y hc hd hann hker hhit
      (by simpa [g,twisted_hessian] using hder)
    have hph : oddGaussPhase ψ ((hasseDeriv 2 g).eval a) d=oddGaussPhase ψ ((hasseDeriv 2 f).eval y) d := by
      rw [show hasseDeriv 2 g=hasseDeriv 2 f from twisted_hasse f b]
      exact odd_phase_constant ψ d _ _ kill (eval_same_residue _ ha)
    rw [hdv,sub_eq_zero] at hr
    rw [hph] at hn hs
    exact ⟨a,ha,hr,hn,by simpa only [hev] using hs⟩

#print axioms nonstationary_branch_zero
#print axioms odd_fourier_branch
end WaringLinear
