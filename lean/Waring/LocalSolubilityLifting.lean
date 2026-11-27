import Waring.LocalSolubilityPrime
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! # Explicit power-sum lifting at good and exceptional primes

The exceptional eighth-power and ninth-power expansions are integer
identities. A finite-field linear correction then lifts every target in
the specified base congruence class through all higher prime powers.
-/

noncomputable section
namespace Waring.LocalSolubility

theorem power_lift_step {k p : ℕ} (hp : p.Prime) {B D m x target : ℤ}
    (c : ℤ → ℤ) (hD : (p : ℤ) ∣ D)
    (hc : (c x : ZMod p) ≠ 0)
    (hlaw : ∀ t : ℤ,∃ w : ℤ,
      (x+D*m*t)^k=x^k+B*m*c x*t+B*m*(p : ℤ)*w)
    (hsol : B*m ∣ x^k-target) :
    ∃ y : ℤ,B*m*(p : ℤ) ∣ y^k-target ∧ (y : ZMod p)=(x : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z,hz⟩ := hsol
  let t : ℤ := ((-(z : ZMod p)/(c x : ZMod p)).val : ℤ)
  have ht : ((z+c x*t : ℤ) : ZMod p)=0 := by
    simp only [Int.cast_add,Int.cast_mul,t,Int.cast_natCast,ZMod.natCast_zmod_val]
    field_simp [hc]
    ring
  have hdiv : (p : ℤ) ∣ z+c x*t :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ht
  obtain ⟨v,hv⟩ := hdiv
  obtain ⟨w,hw⟩ := hlaw t
  refine ⟨x+D*m*t,⟨v+w,?_⟩,?_⟩
  · rw [hw]
    calc
      _ = B*m*(z+c x*t)+B*m*(p : ℤ)*w := by linear_combination hz
      _ = _ := by rw [hv]; ring
  · have hDc : (D : ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hD
    simp only [Int.cast_add,Int.cast_mul,hDc,zero_mul,add_zero]

theorem power_lift_all {k p : ℕ} (hp : p.Prime) {B D x₀ target : ℤ}
    (c : ℤ → ℤ) (hD : (p : ℤ) ∣ D)
    (hc : ∀ x : ℤ,(x : ZMod p) ≠ 0 → (c x : ZMod p) ≠ 0)
    (hlaw : ∀ x m t : ℤ,∃ w : ℤ,
      (x+D*m*t)^k=x^k+B*m*c x*t+B*m*(p : ℤ)*w)
    (hbase : B ∣ x₀^k-target) (hunit : (x₀ : ZMod p) ≠ 0) (r : ℕ) :
    ∃ y : ℤ,B*(p : ℤ)^r ∣ y^k-target ∧ (y : ZMod p)=(x₀ : ZMod p) := by
  induction r with
  | zero => exact ⟨x₀,by simpa using hbase,rfl⟩
  | succ r ih =>
      obtain ⟨x,hx,hxu⟩ := ih
      obtain ⟨y,hy,hyu⟩ := power_lift_step hp c hD (hc x (hxu ▸ hunit))
        (hlaw x ((p : ℤ)^r)) hx
      refine ⟨y,?_,hyu.trans hxu⟩
      simpa only [pow_succ,mul_assoc] using hy

theorem good_power_lift_identity (k p : ℕ) (x m t : ℤ) :
    ∃ w : ℤ,(x+(p : ℤ)*m*t)^k=
      x^k+(p : ℤ)*m*((k : ℤ)*x^(k-1))*t+(p : ℤ)*m*(p : ℤ)*w := by
  obtain ⟨q,hq⟩ := (Polynomial.X^k : Polynomial ℤ).binomExpansion x ((p : ℤ)*m*t)
  simp only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.derivative_X_pow,
    Polynomial.eval_mul,Polynomial.eval_C] at hq
  refine ⟨q*m*t^2,?_⟩
  rw [hq]
  ring

theorem good_prime_power_lifts {k p : ℕ} (hp : p.Prime) (hpk : ¬ p ∣ k)
    {x target : ℤ} (hbase : (p : ℤ) ∣ x^k-target)
    (hunit : (x : ZMod p) ≠ 0) (r : ℕ) :
    ∃ y : ℤ,(p : ℤ)^(r+1) ∣ y^k-target ∧ (y : ZMod p)=(x : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hk : (k : ZMod p) ≠ 0 := by
    intro hz
    exact hpk ((ZMod.natCast_zmod_eq_zero_iff_dvd k p).mp hz)
  have h := power_lift_all (k := k) hp (B := (p : ℤ)) (D := (p : ℤ))
    (fun z => (k : ℤ)*z^(k-1)) (dvd_refl _)
    (by
      intro z hz
      simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_pow] using mul_ne_zero hk (pow_ne_zero _ hz))
    (good_power_lift_identity k p) hbase hunit r
  simpa only [pow_succ',Nat.succ_eq_add_one] using h

theorem eighth_power_lift_identity (x m t : ℤ) :
    ∃ w : ℤ,(x+4*m*t)^8=x^8+32*m*x^7*t+32*m*2*w := by
  refine ⟨7*x^6*m*t^2+56*x^5*m^2*t^3+280*x^4*m^3*t^4+
    896*x^3*m^4*t^5+1792*x^2*m^5*t^6+2048*x*m^6*t^7+1024*m^7*t^8,?_⟩
  ring

theorem ninth_power_lift_identity (x m t : ℤ) :
    ∃ w : ℤ,(x+3*m*t)^9=x^9+27*m*x^8*t+27*m*3*w := by
  refine ⟨4*x^7*m*t^2+28*x^6*m^2*t^3+126*x^5*m^3*t^4+
    378*x^4*m^4*t^5+756*x^3*m^5*t^6+972*x^2*m^6*t^7+
    729*x*m^7*t^8+243*m^8*t^9,?_⟩
  ring

theorem eighth_two_power_lifts {x target : ℤ} (hbase : (32 : ℤ) ∣ x^8-target)
    (hunit : (x : ZMod 2) ≠ 0) (r : ℕ) :
    ∃ y : ℤ,(2 : ℤ)^(r+5) ∣ y^8-target ∧ (y : ZMod 2)=(x : ZMod 2) := by
  have h := power_lift_all (k := 8) (p := 2) Nat.prime_two (B := 32) (D := 4)
    (fun z => z^7) (by norm_num)
    (by intro z hz; simpa only [Int.cast_pow] using pow_ne_zero 7 hz)
    eighth_power_lift_identity hbase hunit r
  convert h using 1 <;> norm_num [pow_add,mul_comm]

theorem ninth_three_power_lifts {x target : ℤ} (hbase : (27 : ℤ) ∣ x^9-target)
    (hunit : (x : ZMod 3) ≠ 0) (r : ℕ) :
    ∃ y : ℤ,(3 : ℤ)^(r+3) ∣ y^9-target ∧ (y : ZMod 3)=(x : ZMod 3) := by
  have h := power_lift_all (k := 9) (p := 3) Nat.prime_three (B := 27) (D := 3)
    (fun z => z^8) (by norm_num)
    (by intro z hz; simpa only [Int.cast_pow] using pow_ne_zero 8 hz)
    ninth_power_lift_identity hbase hunit r
  convert h using 1 <;> norm_num [pow_add,mul_comm]

#print axioms good_prime_power_lifts
#print axioms eighth_two_power_lifts
#print axioms ninth_three_power_lifts
end Waring.LocalSolubility
