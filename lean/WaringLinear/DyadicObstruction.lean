import Waring.Representation
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # The dyadic obstruction to uniform linear Waring bounds -/
open scoped BigOperators
namespace WaringLinear

private theorem odd_square (x : ℕ) (hx : x % 2 = 1) : ∃ b : ℕ, x^2 = 8*b+1 := by
  let a := x/2
  have he : x = 2*a+1 := by unfold a; omega
  let c := a/2
  by_cases h : a%2=0
  · have h' : a=2*c := by unfold c; omega
    refine ⟨2*c^2+c, ?_⟩
    rw [he,h']; ring
  · have h' : a=2*c+1 := by unfold c; omega
    refine ⟨2*c^2+3*c+1, ?_⟩
    rw [he,h']; ring

theorem odd_dyadic_power (x : ℕ) (hx : x%2=1) (j : ℕ) :
    ∃ b : ℕ, x^(2^(j+1)) = 4*2^(j+1)*b+1 := by
  induction j with
  | zero => simpa using odd_square x hx
  | succ j ih =>
    obtain ⟨b,hb⟩ := ih
    refine ⟨2*2^(j+1)*b^2+b, ?_⟩
    rw [show 2^(j+1+1) = 2^(j+1)*2 by rw [pow_succ], pow_mul, hb]
    ring

private theorem even_power_divisibility (x : ℕ) (hx : x%2=0) (j : ℕ) :
    8*2^(j+3) ∣ x^(2^(j+3)) := by
  have hle : j+6 ≤ 2^(j+3) := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show 2^(j+1+3) = 2^(j+3)*2 by rw [show j+1+3=j+3+1 by omega,pow_succ]]
      omega
  have he : 8*2^(j+3) = 2^(j+6) := by
    calc
      _ = 2^3*2^(j+3) := by norm_num
      _ = 2^(3+(j+3)) := (pow_add _ _ _).symm
      _ = _ := by congr 1; omega
  rw [he]
  exact (Nat.pow_dvd_pow 2 hle).trans (pow_dvd_pow_of_dvd (Nat.dvd_of_mod_eq_zero hx) _)

/-- For every height, the congruence class 4k modulo 8k supplies a target
with no representation by fewer than 4k terms, for k = 2^(j+3). -/
theorem dyadic_no_representation (j a t : ℕ) (x : Fin t → ℕ)
    (ht : t < 4*2^(j+3)) :
    (∑ i, x i^(2^(j+3))) ≠ 8*2^(j+3)*a+4*2^(j+3) := by
  classical
  let k : ℕ := 2^(j+3)
  have hk : 0 < k := by unfold k; positivity
  let S := Finset.univ.filter (fun i : Fin t => x i % 2 = 1)
  have hsc : S.card < 4*k := (Finset.card_le_univ S).trans_lt (by simpa using ht)
  have hmod (i : Fin t) : x i^k % (4*k) = if x i%2=1 then 1 else 0 := by
    split_ifs with h
    · have hg := odd_dyadic_power (x i) h (j+2)
      change ∃ b : ℕ, x i^k = 4*k*b+1 at hg
      obtain ⟨b,hb⟩ := hg
      rw [hb,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (by omega : 1 < 4*k)]
    · have he := even_power_divisibility (x i) (by omega) j
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_trans (show 4*k ∣ 8*k from ⟨2,by ring⟩) he
  have hsum : (∑ i, x i^k) % (4*k) = S.card := by
    rw [Finset.sum_nat_mod]
    simp_rw [hmod]
    simp only [Finset.sum_boole, Nat.cast_id]
    exact Nat.mod_eq_of_lt hsc
  intro hn
  change (∑ i, x i^k) = 8*k*a+4*k at hn
  have htarget : (8*k*a+4*k) % (4*k) = 0 := Nat.mod_eq_zero_of_dvd
    ⟨2*a+1,by ring⟩
  rw [hn,htarget] at hsum
  have hall (i : Fin t) : x i%2=0 := by
    by_contra hne
    have hi : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i,by omega⟩
    have hcard := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  have hd : 8*k ∣ ∑ i, x i^k :=
    Finset.dvd_sum (fun i _ => even_power_divisibility _ (hall i) j)
  rw [hn] at hd
  have hdiv : 8*k ∣ 4*k := (Nat.dvd_add_iff_right (dvd_mul_right (8*k) a)).mpr hd
  have := Nat.le_of_dvd (by omega : 0 < 4*k) hdiv
  omega

/-- The exact classical, positive-root Waring predicate forces s≥4k. -/
theorem four_k_le_of_dyadic_waringBound (j s : ℕ)
    (hs : Waring.WaringBound (2^(j+3)) s) : 4*2^(j+3) ≤ s := by
  by_contra! h
  obtain ⟨N,hN⟩ := hs
  let k : ℕ := 2^(j+3)
  have hk : 0 < k := by unfold k; positivity
  have hlarge : N ≤ 8*k*N+4*k := (Nat.le_mul_of_pos_left _ (by omega : 0 < 8*k)).trans
    (Nat.le_add_right _ _)
  obtain ⟨t,ht,x,_,heq⟩ := hN _ hlarge
  exact dyadic_no_representation j N t x (ht.trans_lt h) heq

#print axioms four_k_le_of_dyadic_waringBound
end WaringLinear
