import WaringSiegel.WSL4RamanujamDigits
import Mathlib.Algebra.Ring.Subring.Basic

/-! # Rational coefficients integral at the residue prime

The interpolation coefficients only need the image of Z localized away
from p. The following explicit subring and congruence calculation avoid
assuming a coefficient-field embedding into a ramified completed ring.
-/
noncomputable section
namespace WaringSiegel.WSL4Local
variable {R : Type*} [CommRing R]

def rationalPrimeCoefficientRing (p : ℕ) (R : Type*) [CommRing R] : Subring R where
  carrier := {c | ∃a b : ℤ,IsCoprime b (p:ℤ) ∧ (b:R)*c=(a:R)}
  zero_mem' := ⟨0,1,isCoprime_one_left,by simp⟩
  one_mem' := ⟨1,1,isCoprime_one_left,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*d+c*b,b*d,hb.mul_left hd,?_⟩
    push_cast
    calc
      (b:R)*d*(x+y)=d*((b:R)*x)+b*((d:R)*y) := by ring
      _=(a:R)*d+c*b := by rw [hx,hy]; ring
  neg_mem' := by
    rintro x ⟨a,b,hb,hx⟩
    exact ⟨-a,b,hb,by simpa only [Int.cast_neg,mul_neg] using congrArg Neg.neg hx⟩
  mul_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*c,b*d,hb.mul_left hd,?_⟩
    push_cast
    calc
      (b:R)*d*(x*y)=((b:R)*x)*((d:R)*y) := by ring
      _=(a:R)*c := by rw [hx,hy]

theorem mem_rationalPrimeCoefficientRing_intCast (p : ℕ) (a : ℤ) :
    (a:R)∈rationalPrimeCoefficientRing p R :=
  ⟨a,1,isCoprime_one_left,by simp⟩

theorem rationalPrimeCoefficientRing_approx (p t : ℕ) {c : R}
    (hc : c∈rationalPrimeCoefficientRing p R) :
    ∃a : ℤ,∃b : R,c=(a:R)+(p:R)^t*b := by
  obtain ⟨a,b,hb,hc⟩ := hc
  obtain ⟨u,v,hbez⟩ := hb.pow_right (n:=t)
  have hbezR := congrArg (fun x : ℤ => (x:R)) hbez
  push_cast at hbezR
  refine ⟨u*a,(v:R)*c,?_⟩
  push_cast
  linear_combination -c*hbezR+(u:R)*hc

/-- Any such coefficient admits the claimed short integer-power
approximation, with an explicit error divisible by p^t. -/
theorem rationalPrimeCoefficientRing_power_list_approx
    (p n r t : ℕ) [Fact p.Prime] (hn : 0<n) {c : R}
    (hc : c∈rationalPrimeCoefficientRing p R) :
    ∃l : List R, l.length≤n*powerDigitBudget p t ∧
      ∃b : R,c=WSL4.localPowerListSum (n*p^r) l+(p:R)^t*b := by
  obtain ⟨a,b,hc⟩ := rationalPrimeCoefficientRing_approx p t hc
  obtain ⟨l,hlen,z,hz⟩ := int_power_list_mod_prime_power p n r t hn a
  refine ⟨l.map (Int.castRingHom R),by simpa using hlen,b+(z:R),?_⟩
  have hzR := congrArg (fun x : ℤ => (x:R)) hz
  push_cast at hzR
  change (a:R)-(Int.castRingHom R) (WSL4.localPowerListSum (n*p^r) l)=
    (p:R)^t*(z:R) at hzR
  rw [map_localPowerListSum] at hzR
  rw [hc]
  linear_combination hzR

#print axioms rationalPrimeCoefficientRing_approx
#print axioms rationalPrimeCoefficientRing_power_list_approx
end WaringSiegel.WSL4Local
