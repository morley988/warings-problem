import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Divisor selection and gcd averaging in the arithmetic A-process -/

open scoped BigOperators
namespace WaringLinear

private theorem reaches_product (L : List ℕ) (R : ℕ) (T H : ℝ)
    (hT : 0≤T) (hr : (R:ℝ)≤T*H) (hfull : T≤(R:ℝ)*L.prod)
    (hcap : ∀ p∈L, (p:ℝ)≤H) :
    ∃ U V : List ℕ, L=U++V ∧ T≤(R:ℝ)*U.prod ∧ (R:ℝ)*U.prod≤T*H := by
  induction L generalizing R with
  | nil =>
    exact ⟨[],[],rfl,by simpa using hfull,by simpa using hr⟩
  | cons p L ih =>
    by_cases ht : T≤R
    · exact ⟨[],p::L,rfl,by simpa using ht,by simpa using hr⟩
    · have hR : ((R*p:ℕ):ℝ) ≤ T*H := by
        rw [Nat.cast_mul]
        exact mul_le_mul (le_of_not_ge ht) (hcap p (List.mem_cons_self ..)) (Nat.cast_nonneg _) hT
      have hL : T≤((R*p:ℕ):ℝ)*L.prod := by simpa [mul_assoc] using hfull
      obtain ⟨U,V,hl,hu,hv⟩ := ih (R*p) hR hL (fun p hp => hcap p (List.mem_cons_of_mem _ hp))
      exact ⟨p::U,V,by simp [hl],by simpa [mul_assoc] using hu,by simpa [mul_assoc] using hv⟩

/-- A divisor between T and T H which is a multiple of any prescribed
initial divisor R≤T. The only overshoot is the largest prime factor H. -/
theorem exists_smooth_step (q R : ℕ) (T H : ℝ) (hq : 0<q) (hRq : R∣q)
    (hRT : (R:ℝ)≤T) (hTq : T≤q) (hH : 1≤H)
    (hprime : ∀ p : ℕ, p.Prime → p∣q → (p:ℝ)≤H) :
    ∃ B : ℕ, R∣B ∧ B∣q ∧ T≤B ∧ (B:ℝ)≤T*H := by
  obtain ⟨n,hn⟩ := hRq
  have hn0 : n≠0 := by intro h; simp [hn,h] at hq
  let L := n.primeFactorsList
  have hprod : L.prod=n := Nat.prod_primeFactorsList hn0
  have hT : 0≤T := (Nat.cast_nonneg _).trans hRT
  have hh : (R:ℝ)≤T*H := hRT.trans (by simpa using mul_le_mul_of_nonneg_left hH hT)
  have ht : T≤(R:ℝ)*L.prod := by simpa [hprod,hn] using hTq
  have hc : ∀ p∈L, (p:ℝ)≤H := by
    intro p hp
    have hh := Nat.mem_primeFactorsList hn0 |>.mp hp
    exact hprime p hh.1 (hh.2.trans (by rw [hn]; exact dvd_mul_left n R))
  obtain ⟨U,V,hUV,lo,hi⟩ := reaches_product L R T H hT hh ht hc
  refine ⟨R*U.prod,dvd_mul_right ..,⟨V.prod,?_⟩,by simpa using lo,by simpa using hi⟩
  rw [hn,←hprod,hUV,List.prod_append,mul_assoc]

private theorem multiples_through (d H : ℕ) (hd : 0<d) :
    ((Finset.Icc 1 H).filter (fun n => d∣n)).card = H/d := by
  classical
  let f (m : ℕ) := m*d
  have he : (Finset.Icc 1 H).filter (fun n => d∣n) =
      (Finset.Icc 1 (H/d)).image f := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_image]
    constructor
    · rintro ⟨⟨hn,hN⟩,hm⟩
      have hid := Nat.div_mul_cancel hm
      have hp : 0<n/d := by
        by_contra! hz
        rw [Nat.eq_zero_of_le_zero hz,zero_mul] at hid
        omega
      exact ⟨n/d,⟨hp,Nat.div_le_div_right hN⟩,hid⟩
    · rintro ⟨m,⟨hm,hM⟩,rfl⟩
      exact ⟨⟨Nat.mul_pos hm hd,(Nat.le_div_iff_mul_le hd).1 hM⟩,dvd_mul_left _ _⟩
  rw [he,Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_right hd h)]
  simp

/-- Averaging the gcd of a shift with an arbitrary positive modulus costs
at most its divisor count. -/
theorem gcd_sum_le_divisor_count (H q : ℕ) (hq : q≠0) :
    (∑ h ∈ Finset.Icc 1 H, h.gcd q) ≤ H*q.divisors.card := by
  classical
  have hpoint (h : ℕ) : h.gcd q ≤ ∑ d ∈ q.divisors, if d∣h then d else 0 := by
    have hm : h.gcd q∈q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hq⟩
    have hh := Finset.single_le_sum (f := fun d => if d∣h then d else 0)
      (fun _ _ => Nat.zero_le _) hm
    simpa only [if_pos (Nat.gcd_dvd_left _ _)] using hh
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 H, ∑ d ∈ q.divisors, if d∣h then d else 0 :=
      Finset.sum_le_sum (fun h _ => hpoint h)
    _ = ∑ d ∈ q.divisors, ∑ h ∈ Finset.Icc 1 H, if d∣h then d else 0 := Finset.sum_comm
    _ ≤ ∑ _d ∈ q.divisors, H := by
      apply Finset.sum_le_sum
      intro d hd
      have hpos := Nat.pos_of_mem_divisors hd
      rw [← Finset.sum_filter,Finset.sum_const,multiples_through d H hpos,nsmul_eq_mul]
      exact Nat.div_mul_le_self _ _
    _ = _ := by simp [mul_comm]

#print axioms exists_smooth_step
#print axioms gcd_sum_le_divisor_count
end WaringLinear
