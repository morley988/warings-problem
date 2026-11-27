import WaringSiegel.WSL4MajorRamanujamHenselStep

/-!
# Sharp Ramanujam lifting at the primes dividing an exponent

The precision is r+1 at odd residue characteristic and r+2 at 2.
The congruence of the lifted root is modulo the rational prime p itself,
including in ramified complete local rings.
-/
noncomputable section
set_option maxHeartbeats 1200000
open Polynomial IsLocalRing
open scoped Classical
namespace WaringSiegel.WSL4

/-- The extra precision required for a sharp prime-power lift. -/
def ramanujamLiftOffset (p : ℕ) : ℕ := if p=2 then 2 else 1

def ramanujamLiftPrecision (p r : ℕ) : ℕ := r+ramanujamLiftOffset p

theorem ramanujamLiftOffset_pos (p : ℕ) : 1 ≤ ramanujamLiftOffset p := by
  unfold ramanujamLiftOffset
  split <;> omega

theorem ramanujamLiftPrecision_pos (p r : ℕ) : 0 < ramanujamLiftPrecision p r := by
  have := ramanujamLiftOffset_pos p
  dsimp [ramanujamLiftPrecision]
  omega

theorem prime_lift_scale_inequality (p r : ℕ) (hp : p.Prime) :
    ramanujamLiftPrecision p r+2 ≤ ramanujamLiftPrecision p r*p := by
  have hp2 := hp.two_le
  by_cases he : p=2
  · subst p
    simp only [ramanujamLiftPrecision,ramanujamLiftOffset,ite_true]
    omega
  · have hp3 : 3 ≤ p := by omega
    simp only [ramanujamLiftPrecision,ramanujamLiftOffset,if_neg he]
    nlinarith

variable {A : Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem prime_power_unit_lift_sharp (p : ℕ) (hp : p.Prime)
    [CharP (ResidueField A) p] (r : ℕ) (z c : A) (hz : IsUnit z) :
    ∃ y b : A,
      y^(p^r)=z^(p^r)+(p:A)^(ramanujamLiftPrecision p r)*c ∧
      y=z+(p:A)*b := by
  induction r generalizing c with
  | zero =>
      let a := ramanujamLiftOffset p
      have ha : 1 ≤ a := ramanujamLiftOffset_pos p
      refine ⟨z+(p:A)^a*c,(p:A)^(a-1)*c,?_,?_⟩
      · simp only [pow_zero,pow_one,ramanujamLiftPrecision,zero_add,a]
      · rw [← mul_assoc,← pow_succ',Nat.sub_add_cancel ha]
  | succ r ih =>
      have hd : 1 ≤ ramanujamLiftPrecision p r := by
        have := ramanujamLiftPrecision_pos p r
        omega
      obtain ⟨w,b,hw,hwb⟩ := prime_power_step_hensel p
        (ramanujamLiftPrecision p r) hp hd (prime_lift_scale_inequality p r hp)
        (z^(p^r)) c (hz.pow _)
      obtain ⟨y,t,hy,hyt⟩ := ih b
      have hyw : y^(p^r)=w := hy.trans hwb.symm
      refine ⟨y,t,?_,hyt⟩
      calc
        y^(p^(r+1)) = (y^(p^r))^p := by rw [pow_succ,pow_mul]
        _ = (z^(p^r))^p+(p:A)^(ramanujamLiftPrecision p r+1)*c := by rw [hyw,hw]
        _ = z^(p^(r+1))+(p:A)^(ramanujamLiftPrecision p (r+1))*c := by
          have he : ramanujamLiftPrecision p r+1=ramanujamLiftPrecision p (r+1) := by
            simp only [ramanujamLiftPrecision]
            omega
          rw [← pow_mul,← pow_succ,he]

theorem power_unit_lift_sharp (p n r : ℕ) (hp : p.Prime)
    [CharP (ResidueField A) p] (hn : IsUnit (n:A))
    (z c : A) (hz : IsUnit z) :
    ∃ y b : A,
      y^(n*p^r)=z^(n*p^r)+(p:A)^(ramanujamLiftPrecision p r)*c ∧
      y=z+(p:A)*b := by
  have hq : residue A ((p:A)^(ramanujamLiftPrecision p r))=0 := by
    rw [map_pow,map_natCast,CharP.cast_eq_zero]
    exact zero_pow (ramanujamLiftPrecision_pos p r).ne'
  obtain ⟨w,b,hw,hwb⟩ := unit_power_step_hensel n hn
    ((p:A)^(ramanujamLiftPrecision p r)) hq (z^(p^r)) c (hz.pow _)
  obtain ⟨y,t,hy,hyt⟩ := prime_power_unit_lift_sharp p hp r z b hz
  have hyw : y^(p^r)=w := hy.trans hwb.symm
  refine ⟨y,t,?_,hyt⟩
  calc
    y^(n*p^r) = (y^(p^r))^n := by rw [← pow_mul,Nat.mul_comm n]
    _ = (z^(p^r))^n+(p:A)^(ramanujamLiftPrecision p r)*c := by rw [hyw,hw]
    _ = _ := by rw [← pow_mul,Nat.mul_comm (p^r)]

/-- Ramanujam's sharp congruence criterion, with an actual root in the complete ring. -/
theorem power_root_of_dvd_sharp (p n r : ℕ) (hp : p.Prime)
    [CharP (ResidueField A) p] (hn : IsUnit (n:A))
    (z a : A) (hz : IsUnit z)
    (ha : (p:A)^(ramanujamLiftPrecision p r) ∣ a-z^(n*p^r)) :
    ∃ y : A, y^(n*p^r)=a ∧ (p:A) ∣ y-z ∧ IsUnit y := by
  obtain ⟨c,hc⟩ := ha
  obtain ⟨y,b,hy,hyb⟩ := power_unit_lift_sharp p n r hp hn z c hz
  have hyr : residue A y=residue A z := by
    rw [hyb,map_add,map_mul,map_natCast,CharP.cast_eq_zero,zero_mul,add_zero]
  refine ⟨y,?_,⟨b,by rw [hyb]; ring⟩,?_⟩
  · rw [← hc] at hy
    exact hy.trans (by ring)
  · apply (residue_ne_zero_iff_isUnit y).mp
    rw [hyr]
    exact (residue_ne_zero_iff_isUnit z).mpr hz

#print axioms prime_power_unit_lift_sharp
#print axioms power_unit_lift_sharp
#print axioms power_root_of_dvd_sharp
end WaringSiegel.WSL4
