import WaringSiegel.WSL4WeilHensel
import Mathlib.Data.ZMod.Basic

/-! # An integral polynomial with affine residue reduction is surjective

The lift is the proved arbitrary-polynomial Newton/Hensel theorem in an
adic-complete local ring. There is no monicity requirement.
-/
noncomputable section
open Polynomial IsLocalRing
namespace WaringSiegel.WSL4
set_option maxHeartbeats 800000

theorem integer_polynomial_surjective_of_affine_mod_prime
    {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (k : ℕ) [CharP (ResidueField A) k] (F : ℤ[X]) (c : ZMod k)
    (hF : F.map (Int.castRingHom (ZMod k))=X+C c) :
    ∀z : A,∃t : A,F.eval₂ (Int.castRingHom A) t=z := by
  let j : ZMod k →+* ResidueField A := ZMod.castHom (dvd_refl k) _
  have hc₁ : (residue A).comp (Int.castRingHom A)=Int.castRingHom (ResidueField A) :=
    RingHom.ext_int _ _
  have hc₂ : j.comp (Int.castRingHom (ZMod k))=Int.castRingHom (ResidueField A) :=
    RingHom.ext_int _ _
  have hred : (F.map (Int.castRingHom A)).map (residue A)=X+C (j c) := by
    calc
      (F.map (Int.castRingHom A)).map (residue A)=
          F.map (Int.castRingHom (ResidueField A)) := by rw [Polynomial.map_map,hc₁]
      _=(F.map (Int.castRingHom (ZMod k))).map j := by rw [Polynomial.map_map,hc₂]
      _=X+C (j c) := by rw [hF]; simp only [Polynomial.map_add,map_X,map_C]
  intro z
  let f : A[X] := F.map (Int.castRingHom A)-C z
  let a₀ : ResidueField A := residue A z-j c
  have hfmap : f.map (residue A)=X+C (j c-residue A z) := by
    simp only [f,Polynomial.map_sub,map_C]
    rw [hred,C_sub]
    ring
  have hroot : f.eval₂ (residue A) a₀=0 := by
    rw [eval₂_eq_eval_map,hfmap]
    simp only [eval_add,eval_X,eval_C,a₀]
    ring
  have hder : f.derivative.eval₂ (residue A) a₀≠0 := by
    rw [eval₂_eq_eval_map,← derivative_map,hfmap]
    simp only [derivative_add,derivative_X,derivative_C,add_zero,eval_one,ne_eq,one_ne_zero,not_false_eq_true]
  obtain ⟨t,ht,-⟩ := WSL4Weil.local_adic_simple_root_lift f a₀ hroot hder
  refine ⟨t,sub_eq_zero.mp ?_⟩
  simpa only [f,eval_sub,eval_map,eval_C] using ht

#print axioms integer_polynomial_surjective_of_affine_mod_prime
end WaringSiegel.WSL4
