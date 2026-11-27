import Waring.EndgameCompletionCompleteSums
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Elementary twisted complete sums at prime moduli

The fourth moment over the two coefficients counts simultaneous sums
and power sums. A polynomial root bound controls that energy; rescaling
along a nonzero linear-coefficient orbit gives exponent three quarters.
This is the elementary Davenport--Heilbronn substitute for the stronger
Weil estimate in Vaughan's major-arc approximation.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Waring.EndgameCompletion

theorem fixed_sum_power_polynomial_ne_zero {K : Type*} [Field K]
    (k : ℕ) (hk : 2 ≤ k) (hk0 : (k : K) ≠ 0) (s c : K) (hs : s ≠ 0) :
    (Polynomial.X^k+(Polynomial.C s-Polynomial.X)^k-Polynomial.C c : Polynomial K) ≠ 0 := by
  let F : Polynomial K := Polynomial.X^k+(Polynomial.C s-Polynomial.X)^k-Polynomial.C c
  have hderiv : F.derivative.eval 0=-(k : K)*s^(k-1) := by
    simp [F, Polynomial.derivative_pow, show k-1 ≠ 0 by omega]
  intro hzero
  have hz : F=0 := hzero
  rw [hz, Polynomial.derivative_zero, Polynomial.eval_zero] at hderiv
  exact (mul_ne_zero (neg_ne_zero.mpr hk0) (pow_ne_zero _ hs)) hderiv.symm

theorem fixed_sum_power_polynomial_natDegree_le {K : Type*} [Field K]
    (k : ℕ) (s c : K) :
    (Polynomial.X^k+(Polynomial.C s-Polynomial.X)^k-Polynomial.C c : Polynomial K).natDegree ≤ k := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · calc
        _ ≤ k*(Polynomial.C s-Polynomial.X : Polynomial K).natDegree := Polynomial.natDegree_pow_le
        _ ≤ k*1 := Nat.mul_le_mul_left k (by
          simpa using
            Polynomial.natDegree_sub_le (Polynomial.C s) (Polynomial.X : Polynomial K))
        _ = k := Nat.mul_one k
  · simp

theorem card_fixed_sum_power_fiber_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (k : ℕ) (hk : 2 ≤ k) (hk0 : (k : K) ≠ 0) (s c : K) (hs : s ≠ 0) :
    ((Finset.univ : Finset K).filter (fun x => x^k+(s-x)^k=c)).card ≤ k := by
  have hpoly := fixed_sum_power_polynomial_ne_zero k hk hk0 s c hs
  have hh := Polynomial.card_le_degree_of_subset_roots
    (p := (Polynomial.X^k+(Polynomial.C s-Polynomial.X)^k-Polynomial.C c : Polynomial K))
    (Z := (Finset.univ : Finset K).filter (fun x => x^k+(s-x)^k=c)) (by
      intro x hx
      rw [Polynomial.mem_roots hpoly]
      simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using (Finset.mem_filter.mp hx).2)
  exact hh.trans (fixed_sum_power_polynomial_natDegree_le k s c)

def twistedMonomialSumMod (q : ℕ) [NeZero q] (k : ℕ) (a b : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar (a*x^k+b*x)

def twoParameterCharacterSum {ι : Type*} [Fintype ι] (q : ℕ) [NeZero q]
    (f g : ι → ZMod q) (c : ZMod q × ZMod q) : ℂ :=
  ∑ x : ι, ZMod.stdAddChar (c.1*f x+c.2*g x)

theorem stdAddChar_dot_sum (q : ℕ) [NeZero q] (u v : ZMod q) :
    (∑ c : ZMod q × ZMod q, ZMod.stdAddChar (c.1*u+c.2*v)) =
      if u=0 ∧ v=0 then (q : ℂ)^2 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul]
  rw [← Fintype.sum_mul_sum]
  have hu : (∑ x : ZMod q, ZMod.stdAddChar (x*u))=if u=0 then (q : ℂ) else 0 := by
    simpa only [mul_comm] using stdAddChar_mul_sum q u
  have hv : (∑ x : ZMod q, ZMod.stdAddChar (x*v))=if v=0 then (q : ℂ) else 0 := by
    simpa only [mul_comm] using stdAddChar_mul_sum q v
  rw [hu, hv]
  split_ifs <;> simp_all [pow_two]

theorem twoParameterCharacterSum_norm_sq {ι : Type*} [Fintype ι]
    (q : ℕ) [NeZero q] (f g : ι → ZMod q) (c : ZMod q × ZMod q) :
    ((‖twoParameterCharacterSum q f g c‖^2 : ℝ) : ℂ) =
      ∑ x : ι, ∑ y : ι, ZMod.stdAddChar (c.1*(f x-f y)+c.2*(g x-g y)) := by
  unfold twoParameterCharacterSum
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Exact orthogonality for two finite-field frequencies. -/
theorem twoParameterCharacterSum_second_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℕ) [NeZero q] (f g : ι → ZMod q) :
    (∑ c : ZMod q × ZMod q, ‖twoParameterCharacterSum q f g c‖^2) =
      (q : ℝ)^2*∑ x : ι,
        (((Finset.univ : Finset ι).filter (fun y => f y=f x ∧ g y=g x)).card : ℝ) := by
  have hc : ((∑ c : ZMod q × ZMod q, ‖twoParameterCharacterSum q f g c‖^2 : ℝ) : ℂ) =
      (q : ℂ)^2*∑ x : ι,
        (((Finset.univ : Finset ι).filter (fun y => f y=f x ∧ g y=g x)).card : ℂ) := by
    simp only [Complex.ofReal_sum, twoParameterCharacterSum_norm_sq]
    rw [Finset.sum_comm]
    calc
      _ = ∑ x : ι, ∑ y : ι, ∑ c : ZMod q × ZMod q,
          ZMod.stdAddChar (c.1*(f x-f y)+c.2*(g x-g y)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = ∑ x : ι, ∑ y : ι, if f y=f x ∧ g y=g x then (q : ℂ)^2 else 0 := by
        simp only [stdAddChar_dot_sum, sub_eq_zero, eq_comm]
      _ = _ := by
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  exact_mod_cast hc

theorem twistedMonomialSumMod_sq (q : ℕ) [NeZero q] (k : ℕ) (a b : ZMod q) :
    (twistedMonomialSumMod q k a b)^2 =
      twoParameterCharacterSum q (fun x : ZMod q × ZMod q => x.1^k+x.2^k)
        (fun x => x.1+x.2) (a,b) := by
  unfold twistedMonomialSumMod twoParameterCharacterSum
  rw [pow_two, Fintype.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem card_pairs_fixed_sum_le {K : Type*} [AddGroup K] [Fintype K] [DecidableEq K]
    (A : Finset (K × K)) (s : K) (hA : ∀ x ∈ A, x.1+x.2=s) : A.card ≤ Fintype.card K := by
  apply (Finset.card_le_card_of_injOn Prod.fst (t := Finset.univ) (fun _ _ => Finset.mem_univ _) ?_).trans
    (le_of_eq Finset.card_univ)
  intro x hx y hy hxy
  apply Prod.ext hxy
  apply add_left_cancel (a := x.1)
  calc
    _ = s := hA x hx
    _ = y.1+y.2 := (hA y hy).symm
    _ = _ := by rw [hxy]

def pairSumPowerFiber {K : Type*} [CommRing K] [Fintype K] [DecidableEq K]
    (k : ℕ) (x : K × K) : Finset (K × K) :=
  Finset.univ.filter (fun y => y.1^k+y.2^k=x.1^k+x.2^k ∧ y.1+y.2=x.1+x.2)

theorem pairSumPowerFiber_card_le_card {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (k : ℕ) (x : K × K) : (pairSumPowerFiber k x).card ≤ Fintype.card K :=
  card_pairs_fixed_sum_le _ (x.1+x.2) (fun _y hy => (Finset.mem_filter.mp hy).2.2)

theorem pairSumPowerFiber_card_le_degree {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (k : ℕ) (hk : 2 ≤ k) (hk0 : (k : K) ≠ 0) (x : K × K) (hx : x.1+x.2 ≠ 0) :
    (pairSumPowerFiber k x).card ≤ k := by
  apply le_trans (Finset.card_le_card_of_injOn Prod.fst
    (t := Finset.univ.filter (fun z : K => z^k+(x.1+x.2-z)^k=x.1^k+x.2^k)) ?_ ?_)
    (card_fixed_sum_power_fiber_le k hk hk0 (x.1+x.2) (x.1^k+x.2^k) hx)
  · intro y hy
    have hys := (Finset.mem_filter.mp hy).2.2
    have hy2 : x.1+x.2-y.1=y.2 := by linear_combination -hys
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hy2]
      exact (Finset.mem_filter.mp hy).2.1⟩
  · intro y hy z hz hyz
    apply Prod.ext hyz
    have hy' := (Finset.mem_filter.mp hy).2.2
    have hz' := (Finset.mem_filter.mp hz).2.2
    linear_combination hy' - hz' - hyz

/-- Elementary energy bound for simultaneous sum and power-sum equality.
The sum-zero fiber is bounded separately, so no parity case is needed. -/
theorem pairSumPower_energy_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (k : ℕ) (hk : 2 ≤ k) (hk0 : (k : K) ≠ 0) :
    (∑ x : K × K, (pairSumPowerFiber k x).card) ≤ (k+1)*(Fintype.card K)^2 := by
  let Z : Finset (K × K) := Finset.univ.filter (fun x => x.1+x.2=0)
  have hZ : Z.card ≤ Fintype.card K :=
    card_pairs_fixed_sum_le Z 0 (fun x hx => (Finset.mem_filter.mp hx).2)
  calc
    _ ≤ ∑ x : K × K, (k+if x.1+x.2=0 then Fintype.card K else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x.1+x.2=0
      · rw [if_pos hx]
        exact (pairSumPowerFiber_card_le_card k x).trans (Nat.le_add_left _ _)
      · rw [if_neg hx, add_zero]
        exact pairSumPowerFiber_card_le_degree k hk hk0 x hx
    _ = (Fintype.card K)^2*k+Z.card*Fintype.card K := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        ← Finset.sum_filter]
      simp only [Z, pow_two, Nat.cast_id]
    _ ≤ (Fintype.card K)^2*k+(Fintype.card K)^2 := by
      apply Nat.add_le_add_left
      simpa only [pow_two] using Nat.mul_le_mul_right (Fintype.card K) hZ
    _ = _ := by ring

/-- Fourth moment over both coefficients, proved by exact orthogonality
and a one-variable polynomial fiber bound. -/
theorem twistedMonomialSumMod_fourth_moment_le {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 2 ≤ k) (hpk : ¬ p ∣ k) :
    (∑ c : ZMod p × ZMod p, ‖twistedMonomialSumMod p k c.1 c.2‖^4) ≤
      (k+1 : ℝ)*(p : ℝ)^4 := by
  have hk0 : (k : ZMod p) ≠ 0 := by
    simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using hpk
  have henergy := pairSumPower_energy_le (K := ZMod p) k hk hk0
  have hnorm (c : ZMod p × ZMod p) :
      ‖twistedMonomialSumMod p k c.1 c.2‖^4 =
      ‖twoParameterCharacterSum p (fun x : ZMod p × ZMod p => x.1^k+x.2^k)
        (fun x => x.1+x.2) c‖^2 := by
    rw [← twistedMonomialSumMod_sq p k c.1 c.2, norm_pow, ← pow_mul]
  simp_rw [hnorm]
  rw [twoParameterCharacterSum_second_moment]
  have he : (∑ x : ZMod p × ZMod p, ((pairSumPowerFiber k x).card : ℝ)) ≤
      (k+1 : ℝ)*(p : ℝ)^2 := by
    exact_mod_cast (show (∑ x : ZMod p × ZMod p, (pairSumPowerFiber k x).card) ≤
      (k+1)*p^2 by simpa only [ZMod.card] using henergy)
  calc
    _ ≤ (p : ℝ)^2*((k+1)*(p : ℝ)^2) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := by ring

theorem twistedMonomialSumMod_scale {p : ℕ} [Fact p.Prime]
    (k : ℕ) (a b t : ZMod p) (ht : t ≠ 0) :
    twistedMonomialSumMod p k (a*t^k) (b*t)=twistedMonomialSumMod p k a b := by
  unfold twistedMonomialSumMod
  apply Fintype.sum_equiv (Equiv.mulLeft₀ t ht)
  intro x
  simp only [Equiv.mulLeft₀_apply, mul_pow]
  congr 1
  ring

theorem twistedMonomialSumMod_prime_fourth_good {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 2 ≤ k) (hpk : ¬ p ∣ k) (a b : ZMod p) (hb : b ≠ 0) :
    ‖twistedMonomialSumMod p k a b‖^4 ≤ 2*(k+1 : ℝ)*(p : ℝ)^3 := by
  let A : Finset (ZMod p) := Finset.univ.erase 0
  have hfiber (c : ZMod p × ZMod p) :
      (A.filter (fun t => (a*t^k,b*t)=c)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    apply mul_left_cancel₀ hb
    exact congrArg Prod.snd ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm)
  have hh := sum_comp_le_fiber_bound A (fun t => (a*t^k,b*t))
    (fun c => ‖twistedMonomialSumMod p k c.1 c.2‖^4) 1 (fun _ => by positivity) hfiber
  have hleft : (∑ t ∈ A, ‖twistedMonomialSumMod p k (a*t^k) (b*t)‖^4) =
      ((p : ℝ)-1)*‖twistedMonomialSumMod p k a b‖^4 := by
    have heq : ∀ t ∈ A, twistedMonomialSumMod p k (a*t^k) (b*t)=twistedMonomialSumMod p k a b :=
      fun t ht => twistedMonomialSumMod_scale k a b t (Finset.mem_erase.mp ht).1
    simp_rw [Finset.sum_congr rfl (fun t ht => congrArg (fun z : ℂ => ‖z‖^4) (heq t ht))]
    simp only [A, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [Nat.cast_sub (show 1 ≤ p from (Fact.out : p.Prime).one_lt.le), Nat.cast_one]
  change (∑ t ∈ A, ‖twistedMonomialSumMod p k (a*t^k) (b*t)‖^4) ≤ _ at hh
  rw [hleft, Nat.cast_one, one_mul] at hh
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  apply (mul_le_mul_iff_right₀ (by linarith : (0 : ℝ) < p-1)).mp
  calc
    _ ≤ (k+1 : ℝ)*(p : ℝ)^4 := hh.trans (twistedMonomialSumMod_fourth_moment_le k hk hpk)
    _ ≤ (p-1)*(2*(k+1 : ℝ)*p^3) := by
      have hp : (0 : ℝ) ≤ (k+1 : ℝ)*(p : ℝ)^3 := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hp2) hp]

theorem norm_twistedMonomialSumMod_le (q : ℕ) [NeZero q] (k : ℕ) (a b : ZMod q) :
    ‖twistedMonomialSumMod q k a b‖ ≤ q := by
  unfold twistedMonomialSumMod
  calc
    _ ≤ ∑ x : ZMod q, ‖ZMod.stdAddChar (a*x^k+b*x)‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply, ZMod.card]

/-- The elementary exponent-three-quarters estimate at every prime.
Primes dividing the degree are included using the trivial bound and
the fact that such a prime is at most the degree. -/
theorem twistedMonomialSumMod_prime_fourth_le {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 2 ≤ k) (a b : ZMod p) (hb : b ≠ 0) :
    ‖twistedMonomialSumMod p k a b‖^4 ≤ 2*(k+1 : ℝ)*(p : ℝ)^3 := by
  by_cases hpk : p ∣ k
  · have hpLe : (p : ℝ) ≤ k := by
      exact_mod_cast Nat.le_of_dvd (by omega : 0 < k) hpk
    calc
      _ ≤ (p : ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_twistedMonomialSumMod_le p k a b) 4
      _ = (p : ℝ)*p^3 := by ring
      _ ≤ (k : ℝ)*p^3 := mul_le_mul_of_nonneg_right hpLe (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
        (by positivity)
  · exact twistedMonomialSumMod_prime_fourth_good k hk hpk a b hb

#print axioms twistedMonomialSumMod_fourth_moment_le
#print axioms twistedMonomialSumMod_prime_fourth_good
#print axioms twistedMonomialSumMod_prime_fourth_le

#print axioms card_fixed_sum_power_fiber_le
#print axioms twoParameterCharacterSum_second_moment

end Waring.EndgameCompletion
