import WaringSiegel.WSL4MajorRamanujamRelativeRing
import WaringSiegel.WSL4RamanujamCoefficientSharp

/-! # Prime-power digit approximation through an exact finite residue quotient -/
noncomputable section
set_option maxHeartbeats 1200000
open IsLocalRing
open scoped Classical
namespace WaringSiegel.WSL4
open WSL4Local

variable (p : ℕ) [Fact p.Prime]
variable {L : Type*} [Field L] [Finite L] [CharP L p]

theorem finiteField_tame_power_list (n r : ℕ) (hn : 0<n) (a : L)
    (ha : a∈AddSubgroup.closure (Set.range (fun x : L => x^n))) :
    ∃ l : List L,l.length ≤ n ∧ localPowerListSum (n*p^r) l=a := by
  obtain ⟨l,hlen,hl⟩ := finiteField_power_list n hn a ha
  let e := iterateFrobeniusEquiv L p r
  have hpow (x : L) : (e.symm x)^(n*p^r)=x^n := by
    rw [Nat.mul_comm n,pow_mul]
    have he : (e.symm x)^(p^r)=x := e.apply_symm_apply x
    rw [he]
  refine ⟨l.map e.symm,by simpa using hlen,?_⟩
  have he : localPowerListSum (n*p^r) (l.map e.symm)=localPowerListSum n l := by
    clear hlen hl
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons,localPowerListSum_cons,hpow,ih]
  exact he.trans hl

variable {B : Type*} [CommRing B]

theorem quotient_power_list_mod_prime
    (rho : B →+* L) (hsurj : Function.Surjective rho)
    (hker : ∀ b : B,rho b=0 ↔ (p:B) ∣ b)
    (n r : ℕ) (hn : 0<n)
    (hspan : ∀ a : L,a∈AddSubgroup.closure (Set.range (fun x : L => x^n))) (a : B) :
    ∃ l : List B,l.length ≤ n ∧ (p:B) ∣ a-localPowerListSum (n*p^r) l := by
  obtain ⟨l,hlen,hl⟩ := finiteField_tame_power_list p n r hn (rho a) (hspan _)
  choose g hg using hsurj
  refine ⟨l.map g,by simpa using hlen,?_⟩
  apply (hker _).mp
  rw [map_sub,map_localPowerListSum]
  have he : (l.map g).map rho=l := by
    simp [List.map_map,Function.comp_def,hg]
  rw [he,hl,sub_self]

theorem quotient_power_list_mod_prime_power
    (rho : B →+* L) (hsurj : Function.Surjective rho)
    (hker : ∀ b : B,rho b=0 ↔ (p:B) ∣ b)
    (n r t : ℕ) (hn : 0<n)
    (hspan : ∀ a : L,a∈AddSubgroup.closure (Set.range (fun x : L => x^n))) (a : B) :
    ∃ l : List B,l.length ≤ n*powerDigitBudget p t ∧
      (p:B)^t ∣ a-localPowerListSum (n*p^r) l := by
  induction t generalizing a with
  | zero => exact ⟨[],by simp [powerDigitBudget],by simp⟩
  | succ t ih =>
    obtain ⟨l,hlen,b,hb⟩ := quotient_power_list_mod_prime p rho hsurj hker n r hn hspan a
    obtain ⟨m,hm,c,hc⟩ := ih b
    refine ⟨l++repeatPowerList p m,?_,c,?_⟩
    · rw [List.length_append,repeatPowerList_length,powerDigitBudget]
      have hh := Nat.mul_le_mul_left p hm
      nlinarith
    · rw [localPowerListSum_append,localPowerListSum_repeat]
      calc
        a-(localPowerListSum (n*p^r) l+(p:B)*localPowerListSum (n*p^r) m)=
          (a-localPowerListSum (n*p^r) l)-(p:B)*localPowerListSum (n*p^r) m := by ring
        _=(p:B)*(b-localPowerListSum (n*p^r) m) := by rw [hb]; ring
        _=(p:B)^(t+1)*c := by rw [hc,pow_succ]; ring

#print axioms finiteField_tame_power_list
#print axioms quotient_power_list_mod_prime_power
end WaringSiegel.WSL4
