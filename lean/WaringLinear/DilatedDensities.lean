import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Densities under disjoint integral dilations

For dyadic powers, the targets with an odd root form the primitive part B.
Every other represented target is q times a smaller represented target,
where q=2^k. The theorem applies to any such disjoint decomposition.
-/

namespace WaringLinear

noncomputable def countPositive (p : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter p).card

/-- The count of represented targets equals the primitive count plus the
count of represented targets up to the integral quotient. -/
theorem count_dilates {q : ℕ} (hq : 0<q) (R B : ℕ → Prop)
    (hRB : ∀ n, 0<n → (R n ↔ B n ∨ q ∣ n ∧ R (n/q)))
    (hdis : ∀ n, B n → ¬ q ∣ n) (N : ℕ) :
    countPositive R N = countPositive B N + countPositive R (N/q) := by
  classical
  let A := (Finset.Icc 1 N).filter B
  let D := ((Finset.Icc 1 (N/q)).filter R).image (fun m => m*q)
  have h : (Finset.Icc 1 N).filter R = A ∪ D := by
    ext n
    simp only [A,D,Finset.mem_filter,Finset.mem_Icc,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro ⟨⟨hn,hN⟩,hr⟩
      rcases (hRB n hn).1 hr with hb | ⟨hd,hs⟩
      · exact Or.inl ⟨⟨hn,hN⟩,hb⟩
      · right
        have hmul := Nat.div_mul_cancel hd
        have hpos : 0<n/q := by
          by_contra! hz
          rw [Nat.eq_zero_of_le_zero hz,zero_mul] at hmul
          omega
        exact ⟨n/q, ⟨⟨hpos,Nat.div_le_div_right hN⟩,hs⟩, hmul⟩
    · rintro (⟨⟨hn,hN⟩,hb⟩ | ⟨m,⟨⟨hm,hM⟩,hr⟩,rfl⟩)
      · exact ⟨⟨hn,hN⟩,(hRB n hn).2 (Or.inl hb)⟩
      · have hx : 0<m*q := Nat.mul_pos hm hq
        exact ⟨⟨hx,(Nat.le_div_iff_mul_le hq).1 hM⟩,
          (hRB _ hx).2 (Or.inr ⟨dvd_mul_left q m, by simpa [Nat.mul_div_cancel _ hq] using hr⟩)⟩
  have hd : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro n hn hx
    obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hx
    exact hdis _ (Finset.mem_filter.mp hn).2 (dvd_mul_left q m)
  have hi : Function.Injective (fun m : ℕ => m*q) :=
    fun _ _ he => Nat.eq_of_mul_eq_mul_right hq he
  simpa only [countPositive,A,D,Finset.card_image_of_injective _ hi] using
    (congrArg Finset.card h).trans (Finset.card_union_of_disjoint hd)

/-- If the primitive count has density d(1−1/q) with an O(N^u)
error, the full count has density d with an error of the same order.
The scalar majorant D obeys C+d+D/q^u≤D. -/
theorem density_of_dilates {q : ℕ} (hq : 1<q) (A B : ℕ → ℝ)
    (hA : A 0=0) (hrec : ∀ n, 0<n → A n=B n+A (n/q))
    (d C D u : ℝ) (hd : 0≤d) (hD : 0≤D) (hu : 0<u)
    (habs : C+d+D/(q:ℝ)^u ≤ D)
    (hB : ∀ n, 0<n → |B n - d*(1-1/(q:ℝ))*(n:ℝ)| ≤ C*(n:ℝ)^u) :
    ∀ n, |A n-d*(n:ℝ)| ≤ D*(n:ℝ)^u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · simp [hn,hA,Real.zero_rpow hu.ne']
    have hn0 : 0<n := Nat.pos_of_ne_zero hn
    have hqp : 0<(q:ℝ) := by exact_mod_cast (show 0<q by omega)
    have hsmall := ih (n/q) (Nat.div_lt_self hn0 hq)
    have hsum : (n%q:ℝ)+(q:ℝ)*(n/q:ℕ) = n := by
      exact_mod_cast Nat.mod_add_div n q
    have hrem : (n%q:ℝ)<q := by exact_mod_cast Nat.mod_lt n (by omega : 0<q)
    have hrem0 : 0≤(n%q:ℝ) := by positivity
    have hqr : ((n/q:ℕ):ℝ) ≤ (n:ℝ)/q := by
      apply (le_div_iff₀ hqp).2
      linarith
    have hgap : |d*(((n/q:ℕ):ℝ) - (n:ℝ)/q)| ≤ d := by
      rw [abs_mul,abs_of_nonneg hd,abs_of_nonpos (sub_nonpos.mpr hqr)]
      have hh : (n:ℝ)/q - (n/q:ℕ) ≤ 1 := by
        apply (sub_le_iff_le_add).2
        apply (div_le_iff₀ hqp).2
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh hd]
    have hpow : ((n/q:ℕ):ℝ)^u ≤ (n:ℝ)^u/(q:ℝ)^u := by
      rw [← Real.div_rpow (Nat.cast_nonneg n) hqp.le]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hqr hu.le
    have hone : 1≤(n:ℝ)^u := Real.one_le_rpow (by exact_mod_cast hn0) hu.le
    have hid : A n-d*(n:ℝ) =
        (B n-d*(1-1/(q:ℝ))*(n:ℝ)) + (A (n/q)-d*(n/q:ℕ)) +
        d*(((n/q:ℕ):ℝ) - (n:ℝ)/q) := by rw [hrec n hn0]; ring
    rw [hid]
    calc
      _ ≤ |B n-d*(1-1/(q:ℝ))*(n:ℝ)| + |A (n/q)-d*(n/q:ℕ)| +
           |d*(((n/q:ℕ):ℝ)-(n:ℝ)/q)| :=
        (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ ≤ C*(n:ℝ)^u + D*((n:ℝ)^u/(q:ℝ)^u) + d*(n:ℝ)^u :=
        add_le_add (add_le_add (hB n hn0) (hsmall.trans (mul_le_mul_of_nonneg_left hpow hD)))
          (hgap.trans (by nlinarith [mul_le_mul_of_nonneg_left hone hd]))
      _ = (C+d+D/(q:ℝ)^u)*(n:ℝ)^u := by ring
      _ ≤ D*(n:ℝ)^u := mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg (Nat.cast_nonneg _) _)

#print axioms count_dilates
#print axioms density_of_dilates
end WaringLinear
