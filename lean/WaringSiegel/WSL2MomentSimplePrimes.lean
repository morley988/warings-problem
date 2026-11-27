import WaringSiegel.WSL2MomentSchur
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Data.ZMod.Basic

/-!
# Large primes with simple polynomial roots

Rational polynomial coprimality gives a nonzero integer Bézout constant by
actual denominator clearing.  The proved Schur argument then finds primes
outside that constant and every prescribed finite obstruction, so the root
modulo p has nonzero derivative.  No density or Chebotarev theorem is used.
-/

noncomputable section
open Polynomial IsLocalization
open scoped nonZeroDivisors

namespace WaringSiegel.WSL2

theorem integer_polynomial_bezout_constant (f g : ℤ[X])
    (hcop : IsCoprime (f.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ))) :
    ∃c : ℤ, c≠0 ∧ ∃A B : ℤ[X], A*f+B*g=C c := by
  obtain ⟨a,b,hab⟩ := hcop
  obtain ⟨⟨c,hc0⟩,hc⟩ := integerNormalization_map_to_map ℤ⁰ a
  obtain ⟨⟨d,hd0⟩,hd⟩ := integerNormalization_map_to_map ℤ⁰ b
  rw [Algebra.smul_def,Polynomial.algebraMap_apply,Subtype.coe_mk] at hc hd
  rw [mem_nonZeroDivisors_iff_ne_zero] at hc0 hd0
  refine ⟨c*d,mul_ne_zero hc0 hd0,C d*integerNormalization ℤ⁰ a,
    C c*integerNormalization ℤ⁰ b,?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  simp only [Polynomial.map_add,Polynomial.map_mul,map_C,hc,hd,map_mul]
  calc
    _ = (C ((algebraMap ℤ ℚ) c)*C ((algebraMap ℤ ℚ) d)) *
      (a*f.map (algebraMap ℤ ℚ)+b*g.map (algebraMap ℤ ℚ)) := by ring
    _ = _ := by rw [hab,mul_one]

/-- A nonconstant integer polynomial which is coprime to its derivative over Q
has a simple root modulo some prime larger than any bound and avoiding D. -/
theorem polynomial_large_simple_prime_outside
    (f : ℤ[X]) (hf : 0<f.natDegree)
    (hcop : IsCoprime (f.map (algebraMap ℤ ℚ))
      (f.derivative.map (algebraMap ℤ ℚ)))
    (D : ℤ) (hD : D≠0) (k : ℕ) :
    ∃p : ℕ, p.Prime ∧ k<p ∧ ¬(p : ℤ)∣D ∧
      ∃n : ℤ, f.eval n≠0 ∧ (p : ℤ)∣f.eval n ∧ ¬(p : ℤ)∣f.derivative.eval n := by
  obtain ⟨c,hc,A,B,hAB⟩ := integer_polynomial_bezout_constant f f.derivative hcop
  obtain ⟨p,hp,hpk,hpDc,n,hn,hpn⟩ :=
    polynomial_large_prime_divisor_outside f hf (D*c) (mul_ne_zero hD hc) k
  refine ⟨p,hp,hpk,(fun h=>hpDc (dvd_mul_of_dvd_left h c)),n,hn,hpn,?_⟩
  intro hpd
  have hdvd : (p:ℤ)∣A.eval n*f.eval n+B.eval n*f.derivative.eval n :=
    dvd_add (dvd_mul_of_dvd_right hpn _) (dvd_mul_of_dvd_right hpd _)
  have heq := congrArg (fun Q : ℤ[X]=>Q.eval n) hAB
  simp only [eval_add,eval_mul,eval_C] at heq
  rw [heq] at hdvd
  exact hpDc (dvd_mul_of_dvd_right hdvd D)

/-- The same result stated with actual evaluations in the finite residue ring. -/
theorem polynomial_large_simple_root_mod
    (f : ℤ[X]) (hf : 0<f.natDegree)
    (hcop : IsCoprime (f.map (algebraMap ℤ ℚ))
      (f.derivative.map (algebraMap ℤ ℚ)))
    (D : ℤ) (hD : D≠0) (k : ℕ) :
    ∃p : ℕ, p.Prime ∧ k<p ∧ ¬(p : ℤ)∣D ∧ ∃a : ZMod p,
      (f.map (Int.castRingHom (ZMod p))).eval a=0 ∧
      (f.derivative.map (Int.castRingHom (ZMod p))).eval a≠0 := by
  obtain ⟨p,hp,hpk,hpD,n,hn,hpn,hpn'⟩ :=
    polynomial_large_simple_prime_outside f hf hcop D hD k
  refine ⟨p,hp,hpk,hpD,(n:ZMod p),?_,?_⟩
  · rw [eval_map]
    have heval := eval₂_at_apply (p := f) (Int.castRingHom (ZMod p)) n
    change f.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) n)=0
    rw [heval]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpn
  · rw [eval_map]
    have heval := eval₂_at_apply (p := f.derivative) (Int.castRingHom (ZMod p)) n
    change f.derivative.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) n)≠0
    rw [heval]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).not.mpr hpn'

end WaringSiegel.WSL2
