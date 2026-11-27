import WaringLinear.StationaryDetection
import WaringLinear.QuadraticTaylor
import WaringLinear.PrincipalCosetSums
import WaringLinear.OddGaussNormalization

/-! # Exact stationary phase at odd conductor -/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] [IsLocalRing A] [Fintype A]

/-- A finite local branch at odd conductor has an exact quadratic phase of
absolute value one and square-root amplitude. Annihilator conditions are
satisfied in a principal quotient of exponent 2r+1 with r positive. -/
theorem odd_stationary_branch (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (f : A[X]) (c d y : A) (hc : c^2=0) (hd : d^3=0)
    (hann : ∀ x : A, c*x=0 ↔ x∈Ideal.span {d})
    (hker : ∀ x : A, d*x=0 → x∈Ideal.span {d})
    (hy : residue A (f.derivative.eval y)=0) (hder : IsUnit (f.derivative.derivative.eval y)) :
    ∃ a : A, residue A a=residue A y ∧ f.derivative.eval a=0 ∧
      let h := (hasseDeriv 2 f).eval a
      ‖oddGaussPhase ψ h d‖=1 ∧
      (∑ x ∈ Finset.univ.filter (fun x : A => residue A x=residue A y), ψ (f.eval x)) =
        (Real.sqrt (Fintype.card A):ℂ)*ψ (f.eval a)*oddGaussPhase ψ h d := by
  obtain ⟨a,⟨ha,hroot⟩,_⟩ := finite_local_inverse f.derivative y 0 hder (by simpa using hy.symm)
  refine ⟨a,ha,hroot,?_⟩
  let h := (hasseDeriv 2 f).eval a
  have hu : IsUnit (2*h) := by
    rw [show 2*h=f.derivative.derivative.eval a from double_hasse_two f a]
    apply (residue_ne_zero_iff_isUnit _).1
    rw [eval_same_residue f.derivative.derivative ha]
    exact (residue_ne_zero_iff_isUnit _).2 hder
  have hcard : annCard (d^2)=(annCard d)^2 := card_annihilator_squared_of_kernel_in_image d hker
  refine ⟨norm_oddGaussPhase ψ hψ h d hu hcard,?_⟩
  have hres : residue A d=0 := (pow_eq_zero_iff (by decide : (3:ℕ)≠0)).mp
    (by rw [←map_pow,hd,map_zero])
  have detect := stationary_simple_coset_sum ψ hψ f c d a hc hres hann hroot
    ((double_hasse_two f a) ▸ hu)
  have hp := affine_principal_fibre_sum a d (fun x => ψ (f.eval x))
  change (∑ t : A, ψ (f.eval (a+d*t)))=(annCard d:ℂ)*_ at hp
  have hev (t : A) : f.eval (a+d*t)=f.eval a+h*d^2*t^2 := by
    rw [evaluate_cubic_nilpotent_step f a (d*t) (by rw [mul_pow,hd,zero_mul]),hroot,zero_mul,add_zero]
    dsimp [h]; ring
  have count : (annCard d:ℂ)≠0 := Nat.cast_ne_zero.mpr (annCard_pos d).ne'
  rw [←ha,detect]
  apply mul_left_cancel₀ count
  change (annCard d:ℂ)*_ = _
  rw [←hp]
  simp only [hev,ψ.map_add_eq_mul,←Finset.mul_sum]
  unfold oddGaussPhase
  have hcard' : (Real.sqrt (Fintype.card A):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'
  push_cast
  field_simp
  ring

#print axioms odd_stationary_branch
end WaringLinear
