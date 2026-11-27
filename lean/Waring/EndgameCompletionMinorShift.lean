import Waring.EndgameCompletionMinorCompletion
import Waring.EndgameCompletionMinorTranslation

/-!
# Completed shifted projected Weyl moments

The original interval is shifted inside `1,...,2N`, completed with one
kernel independent of the shift, and projected. The exact translation
lemma then removes the common linear modulation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion
open FourierCompletion QuadraticModulation

def positiveNode (N : ℕ) (n : Fin N) : ℤ := (n.val : ℤ)+1

theorem sum_positiveNode_interval {E : Type*} [AddCommMonoid E]
    (N : ℕ) (a : ℤ) (f : ℤ→E) :
    (∑ n : Fin N,f (a+positiveNode N n))=
      ∑ z∈Finset.Icc (a+1) (a+N),f z := by
  classical
  rw [interval_eq_progression]
  have hh : (a+(N : ℤ)+1-(a+1)).toNat=N := by omega
  rw [hh,progression,Finset.sum_image]
  · unfold positiveNode
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ=>f (a+((n : ℤ)+1))) N]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    simp only [one_mul]
    ring
  · intro n _ m _ h
    simp only [one_mul,add_right_inj] at h
    exact_mod_cast h

theorem fourier_eq_e (n : ℤ) (t : ℝ) :
    fourier n (t : UnitAddCircle)=e (t*(n : ℝ)) := by
  rw [fourier_coe_apply]
  unfold e
  congr 1
  push_cast
  ring

def shiftedPolynomialWeight (r : ℕ) (y : ℤ) (θ : ℝ)
    (α : UnitAddTorus (Fin r)) (z : ℤ) : ℂ :=
  e (θ*((z-y : ℤ) : ℝ)^(r+2))*
    UnitAddTorus.mFourier (fun j : Fin r=>(z-y)^(j.val+1)) α

theorem continuous_shiftedPolynomialWeight (r : ℕ) (y : ℤ) (θ : ℝ) (z : ℤ) :
    Continuous (fun α=>shiftedPolynomialWeight r y θ α z) :=
  continuous_const.mul (UnitAddTorus.mFourier _).continuous

theorem shiftedPolynomialWeight_sum (r N : ℕ) (y : ℤ) (θ : ℝ)
    (α : UnitAddTorus (Fin r)) :
    (∑ z∈Finset.Icc (y+1) (y+N),shiftedPolynomialWeight r y θ α z)=
      polynomialTorusSum r (positiveNode N)
        (fun n=>e (θ*(positiveNode N n : ℝ)^(r+2))) α := by
  rw [← sum_positiveNode_interval]
  unfold shiftedPolynomialWeight polynomialTorusSum finiteTorusSum
  simp only [add_sub_cancel_left]

theorem completed_shifted_polynomial_norm (r N : ℕ) (y : ℤ) (θ γ : ℝ)
    (α : UnitAddTorus (Fin r)) :
    ‖modulatedSum (Finset.Icc 1 (2*N : ℕ)) (shiftedPolynomialWeight r y θ α) γ‖=
      ‖polynomialTorusSum r (fun n : Fin (2*N)=>positiveNode (2*N) n-y)
        (fun n=>e (θ*((positiveNode (2*N) n-y : ℤ) : ℝ)^(r+2)+
          γ*((positiveNode (2*N) n-y : ℤ) : ℝ))) α‖ := by
  have he (z : ℤ) : fourier z (γ : UnitAddCircle)=
      e (γ*(y : ℝ))*e (γ*((z-y : ℤ) : ℝ)) := by
    rw [fourier_eq_e,← e_add]
    congr 1
    push_cast
    ring
  have hs : modulatedSum (Finset.Icc 1 (2*N : ℕ)) (shiftedPolynomialWeight r y θ α) γ=
      e (γ*(y : ℝ))*polynomialTorusSum r
        (fun n : Fin (2*N)=>positiveNode (2*N) n-y)
        (fun n=>e (θ*((positiveNode (2*N) n-y : ℤ) : ℝ)^(r+2)+
          γ*((positiveNode (2*N) n-y : ℤ) : ℝ))) α := by
    unfold modulatedSum
    have hsum := sum_positiveNode_interval (2*N) 0
      (fun z=>shiftedPolynomialWeight r y θ α z*fourier z (γ : UnitAddCircle))
    simp only [zero_add] at hsum
    rw [← hsum]
    unfold polynomialTorusSum finiteTorusSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [he]
    dsimp only
    rw [e_add]
    unfold shiftedPolynomialWeight
    ring
  rw [hs,norm_mul,norm_e,one_mul]

def projectedSlice (r s N : ℕ) (t θ : ℝ) : ℝ :=
  projectedMoment r s (positiveNode N)
    (fun n=>e (θ*(positiveNode N n : ℝ)^(r+2)+t*(positiveNode N n : ℝ)^(r+1)))

/-- Actual completed moment after projection: the completion variable has
disappeared, and the missing next coefficient is `-(r+2)*y*theta`. -/
theorem completed_shifted_projected_moment (r s N : ℕ) (hr : 1≤r)
    (y : ℤ) (θ γ : ℝ) :
    (∫ α,‖modulatedSum (Finset.Icc 1 (2*N : ℕ))
      (shiftedPolynomialWeight r y θ α) γ‖^(2*s) ∂unitTorusMeasure r)=
      projectedSlice r s (2*N) (-(r+2 : ℕ)*(y : ℝ)*θ) θ := by
  simp_rw [completed_shifted_polynomial_norm]
  change projectedMoment r s (fun n : Fin (2*N)=>positiveNode (2*N) n-y) _= _
  have hh := projectedMoment_translation r s hr (positiveNode (2*N)) (-y) θ γ
  simp only [← sub_eq_add_neg,Int.cast_neg] at hh
  convert hh using 1 <;> congr 1
  ring

/-- Completion and translation for each shift, with the exact logarithmic
mass retained. -/
theorem projected_interval_completion (r s N y : ℕ) (hr : 1≤r) (hs : 1≤s)
    (hy : y≤N) (θ : ℝ) :
    projectedSlice r s N 0 θ≤completionMass N^(2*s)*
      projectedSlice r s (2*N) (-(r+2 : ℕ)*(y : ℝ)*θ) θ := by
  have hTS : Finset.Icc ((y : ℤ)+1) ((y : ℤ)+N)⊆Finset.Icc 1 (2*N : ℕ) := by
    intro z hz
    rcases Finset.mem_Icc.mp hz with ⟨hl,hu⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hh := torus_family_completion r (2*s) (by omega)
    (Finset.Icc 1 (2*N : ℕ)) (Finset.Icc ((y : ℤ)+1) ((y : ℤ)+N)) hTS
    (shiftedPolynomialWeight r y θ) (continuous_shiftedPolynomialWeight r y θ)
    (fun t=>‖linearWeylSum N t‖) (continuous_linearWeylSum N).norm
    (fun _=>norm_nonneg _) (fun t=>(norm_kernel_integer_interval N y t).le)
  simp_rw [shiftedPolynomialWeight_sum,completed_shifted_projected_moment r s N hr] at hh
  rw [intervalIntegral.integral_mul_const] at hh
  have hleft : (∫ α,‖polynomialTorusSum r (positiveNode N)
      (fun n=>e (θ*(positiveNode N n : ℝ)^(r+2))) α‖^(2*s) ∂unitTorusMeasure r)=
      projectedSlice r s N 0 θ := by simp [projectedSlice,projectedMoment]
  rw [hleft] at hh
  change _≤completionMass N^(2*s-1)*(completionMass N*_ ) at hh
  convert hh using 1
  rw [← mul_assoc,← pow_succ]
  congr 2
  omega

#print axioms completed_shifted_projected_moment
#print axioms projected_interval_completion
end Waring.EndgameCompletion
