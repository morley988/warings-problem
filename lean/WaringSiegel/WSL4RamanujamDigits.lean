import WaringSiegel.WSL4ArchLocalFiniteAll
import WaringSiegel.WSL4ArchLocalTuples
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Short actual power lists modulo rational prime powers

Prime-field Frobenius permits the tame exponent n, rather than the full
exponent n*p^r, in the per-digit count. This is the unramified coefficient
calculation needed by the local interpolation construction.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WSL4

def repeatPowerList {R : Type*} (t : ℕ) (l : List R) : List R :=
  (List.replicate t l).flatten

@[simp] theorem repeatPowerList_length {R : Type*} (t : ℕ) (l : List R) :
    (repeatPowerList t l).length=t*l.length := by
  induction t with
  | zero => simp [repeatPowerList]
  | succ t ih =>
    have he : repeatPowerList (t+1) l=l++repeatPowerList t l := by
      simp [repeatPowerList,List.replicate_succ]
    rw [he,List.length_append,ih,Nat.succ_mul]
    omega

theorem localPowerListSum_repeat {R : Type*} [CommRing R]
    (k t : ℕ) (l : List R) :
    localPowerListSum k (repeatPowerList t l)=(t:R)*localPowerListSum k l := by
  induction t with
  | zero => simp [repeatPowerList]
  | succ t ih =>
    have he : repeatPowerList (t+1) l=l++repeatPowerList t l := by
      simp [repeatPowerList,List.replicate_succ]
    rw [he,localPowerListSum_append,ih,Nat.cast_add,Nat.cast_one]
    ring

theorem map_localPowerListSum {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : ℕ) (l : List R) :
    f (localPowerListSum k l)=localPowerListSum k (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [localPowerListSum_cons,List.map_cons,map_add,map_pow,ih]

theorem int_power_list_mod_prime
    (p n r : ℕ) [Fact p.Prime] (hn : 0<n) (a : ℤ) :
    ∃l : List ℤ,l.length≤n ∧ (p:ℤ)∣a-localPowerListSum (n*p^r) l := by
  have hmem : (a:ZMod p)∈AddSubgroup.closure (Set.range (fun x : ZMod p => x^n)) := by
    have h := (AddSubgroup.closure (Set.range (fun x : ZMod p => x^n))).zsmul_mem
      (one_mem_power_closure n) a
    simpa using h
  obtain ⟨l,hlen,hl⟩ := finiteField_power_list n hn (a:ZMod p) hmem
  let lz : List ℤ := l.map (fun x => (x.val:ℤ))
  refine ⟨lz,by simpa [lz] using hlen,?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [Int.cast_sub]
  have hc : ((localPowerListSum (n*p^r) lz:ℤ):ZMod p)=localPowerListSum n l := by
    change (Int.castRingHom (ZMod p)) (localPowerListSum (n*p^r) lz)=_
    rw [map_localPowerListSum (Int.castRingHom (ZMod p))]
    simp only [lz,List.map_map,Function.comp_def,Int.coe_castRingHom,Int.cast_natCast,
      ZMod.natCast_zmod_val,List.map_id_fun]
    unfold localPowerListSum
    congr 1
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro x hx
    rw [pow_mul,ZMod.pow_card_pow]
  rw [hc,hl,sub_self]

def powerDigitBudget (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => 1+p*powerDigitBudget p t

theorem int_power_list_mod_prime_power
    (p n r t : ℕ) [Fact p.Prime] (hn : 0<n) (a : ℤ) :
    ∃l : List ℤ,l.length≤n*powerDigitBudget p t ∧
      (p:ℤ)^t∣a-localPowerListSum (n*p^r) l := by
  induction t generalizing a with
  | zero => exact ⟨[],by simp [powerDigitBudget],by simp⟩
  | succ t ih =>
    obtain ⟨l,hlen,b,hb⟩ := int_power_list_mod_prime p n r hn a
    obtain ⟨m,hm,c,hc⟩ := ih b
    refine ⟨l++repeatPowerList p m,?_,c,?_⟩
    · rw [List.length_append,repeatPowerList_length,powerDigitBudget]
      have hh := Nat.mul_le_mul_left p hm
      nlinarith
    · rw [localPowerListSum_append,localPowerListSum_repeat]
      calc
        a-(localPowerListSum (n*p^r) l+(p:ℤ)*localPowerListSum (n*p^r) m)=
          (a-localPowerListSum (n*p^r) l)-(p:ℤ)*localPowerListSum (n*p^r) m := by ring
        _=(p:ℤ)*(b-localPowerListSum (n*p^r) m) := by rw [hb]; ring
        _=(p:ℤ)^(t+1)*c := by rw [hc,pow_succ]; ring

theorem powerDigitBudget_eq_sum (p t : ℕ) :
    powerDigitBudget p t=∑i∈Finset.range t,p^i := by
  induction t with
  | zero => simp [powerDigitBudget]
  | succ t ih =>
    rw [powerDigitBudget,ih,Finset.sum_range_succ']
    simp only [pow_zero,pow_succ',← Finset.mul_sum]
    omega

#print axioms int_power_list_mod_prime
#print axioms int_power_list_mod_prime_power
end WaringSiegel.WSL4Local
