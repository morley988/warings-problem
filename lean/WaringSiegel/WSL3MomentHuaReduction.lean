import WaringSiegel.WSL3MomentHuaCubes
import WaringSiegel.WSL3MomentHuaFibers
import WaringSiegel.WSL2MomentVinogradov

/-!
# Exact all-order Hua moment reduction

The iterated cube aggregate is expanded only after multiplication by the
previous even moment and Haar integration.  Orthogonality gives literal
iterated-difference fibers, whose overlap restrictions may then be dropped.
-/

noncomputable section
open Finset MeasureTheory Polynomial
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

theorem sum_pi_subtype {R T : Type*} [AddCommMonoid T] (H : Finset R) (J : ℕ)
    (f : (Fin J → R) → T) :
    (∑ h : Fin J → H, f (fun i => h i)) =
      ∑ h ∈ Fintype.piFinset (fun _ : Fin J => H), f h := by
  apply Finset.sum_bij (fun h _ => fun i => (h i : R))
  · intro h hh
    exact Fintype.mem_piFinset.mpr (fun i => (h i).property)
  · intro h hh t ht heq
    funext i
    exact Subtype.ext (congrFun heq i)
  · intro h hh
    refine ⟨fun i => ⟨h i, Fintype.mem_piFinset.mp hh i⟩, Finset.mem_univ _, rfl⟩
  · intro h hh
    rfl

variable {R ι : Type*} [CommRing R] [Fintype ι]

local instance huaPeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance huaHaarProbability : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

theorem finiteFrequencySum_eq_frequencySum (S : Finset R) (v : R → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    finiteFrequencySum S v θ = frequencySum (fun x : S => v x) (fun _ => 1) θ := by
  simp only [finiteFrequencySum, frequencySum, one_mul]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _

theorem norm_frequencySum_even_expansion {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (s : ℕ) (θ : ι → AddCircle (1 : ℝ)) :
    ((‖frequencySum v (fun _ => 1) θ‖ ^ (2 * s) : ℝ) : ℂ) =
      frequencySum (fun xy : (Fin s → α) × (Fin s → α) =>
        (∑ i, v (xy.1 i)) - ∑ i, v (xy.2 i)) (fun _ => 1) θ := by
  have hn : ‖frequencySum v (fun _ => 1) θ‖ ^ (2 * s) =
      ‖frequencySum v (fun _ => 1) θ ^ s‖ ^ 2 := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm]
  rw [hn, Complex.ofReal_pow, ← Complex.mul_conj', frequencySum_pow,
    frequencySum_mul_conj_expansion]
  simp only [Finset.prod_const_one, map_one, mul_one, frequencySum, one_mul]

def tuplePowerDifference (k s : ℕ) (S : Finset R)
    (xy : (Fin s → S) × (Fin s → S)) : R :=
  (∑ i, (xy.1 i : R) ^ k) - ∑ i, (xy.2 i : R) ^ k

theorem iteratedFrequency_polynomial_eval (coord : R →+ (ι → ℤ)) (p : R[X])
    (J : ℕ) (h : Fin J → R) (x : R) :
    iteratedFrequency (fun x => coord (p.eval x)) J h x =
      coord ((iteratedPolynomialDifference p J h).eval x) := by
  induction J generalizing x with
  | zero => rfl
  | succ J ih => simp only [iteratedFrequency, iteratedPolynomialDifference,
      polynomialDifference_eval, ih, map_sub]

theorem iteratedCubeSum_ofReal_re (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (J : ℕ) (hJ : 1 ≤ J)
    (v : R → ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    ((iteratedCubeSum S H J v θ).re : ℂ) = iteratedCubeSum S H J v θ := by
  obtain ⟨J, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [iteratedCubeSum_succ S H hH]
  simp only [Complex.re_sum, Complex.ofReal_sum, Complex.ofReal_re]

theorem continuous_iteratedCubeSum (S H : Finset R) (J : ℕ) (v : R → ι → ℤ) :
    Continuous (iteratedCubeSum S H J v) :=
  continuous_finset_sum _ (fun _ _ => continuous_finiteFrequencySum _ _)

theorem iteratedDifferenceFiber_card_real (S H : Finset R) (k J : ℕ) (a : R) :
    ((iteratedDifferenceFiber S H k J a).card : ℝ) =
      ∑ h : Fin J → H, ∑ x ∈ S,
        if (iteratedPolynomialDifference (X ^ k : R[X]) J (fun i => (h i : R))).eval x = a then (1 : ℝ) else 0 := by
  rw [sum_pi_subtype H J (fun h => ∑ x ∈ S,
    if (iteratedPolynomialDifference (X ^ k : R[X]) J h).eval x = a then (1 : ℝ) else 0)]
  simp only [iteratedDifferenceFiber, Finset.card_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.product_eq_sprod, Finset.sum_product]

/-- The previous even moment times the real cube aggregate is at most the
sum of its complete arithmetic fibers.  All quantities are literal. -/
theorem integral_even_mul_iteratedCube_le_fibers (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (k s J : ℕ) (hJ : 1 ≤ J) :
    (∫ θ, ‖finiteFrequencySum S (fun x => coord (x ^ k)) θ‖ ^ (2 * s) *
      (iteratedCubeSum S H J (fun x => coord (x ^ k)) θ).re ∂latticeHaar) ≤
      ∑ xy : (Fin s → S) × (Fin s → S),
        ((iteratedDifferenceFiber S H k J (tuplePowerDifference k s S xy)).card : ℝ) := by
  let v : R → ι → ℤ := fun x => coord (x ^ k)
  let U : (Fin s → S) × (Fin s → S) → ι → ℤ :=
    fun xy => (∑ i, v (xy.1 i)) - ∑ i, v (xy.2 i)
  have hU (xy : (Fin s → S) × (Fin s → S)) : U xy = coord (tuplePowerDifference k s S xy) := by
    simp only [U, v, tuplePowerDifference, map_sub, map_sum]
  have hexp (θ : ι → AddCircle (1 : ℝ)) :
      ((‖finiteFrequencySum S v θ‖ ^ (2 * s) * (iteratedCubeSum S H J v θ).re : ℝ) : ℂ) =
        ∑ h : Fin J → H, frequencySum U (fun _ => 1) θ *
          conj (frequencySum (fun x : iteratedOverlap S J (fun i => h i) =>
            iteratedFrequency v J (fun i => h i) x) (fun _ => 1) θ) := by
    rw [Complex.ofReal_mul, finiteFrequencySum_eq_frequencySum,
      norm_frequencySum_even_expansion]
    have hreal := congrArg conj (iteratedCubeSum_ofReal_re S H hH J hJ v θ)
    rw [Complex.conj_ofReal] at hreal
    rw [hreal, iteratedCubeSum, map_sum, Finset.mul_sum]
    simp only [finiteFrequencySum_eq_frequencySum, U]
  have hint (h : Fin J → H) : Integrable (fun θ =>
      frequencySum U (fun _ => 1) θ *
        conj (frequencySum (fun x : iteratedOverlap S J (fun i => h i) =>
          iteratedFrequency v J (fun i => h i) x) (fun _ => 1) θ)) latticeHaar :=
    ((continuous_frequencySum _ _).mul ((continuous_frequencySum _ _).star)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hid : (∫ θ, ‖finiteFrequencySum S v θ‖ ^ (2 * s) * (iteratedCubeSum S H J v θ).re ∂latticeHaar) =
      ∑ xy : (Fin s → S) × (Fin s → S), ∑ h : Fin J → H,
        ∑ x : iteratedOverlap S J (fun i => h i),
          if coord (tuplePowerDifference k s S xy) =
            coord ((iteratedPolynomialDifference (X ^ k : R[X]) J (fun i => (h i : R))).eval x) then (1 : ℝ) else 0 := by
    calc
      _ = (∫ θ, ((‖finiteFrequencySum S v θ‖ ^ (2 * s) *
            (iteratedCubeSum S H J v θ).re : ℝ) : ℂ) ∂latticeHaar).re := by
        rw [integral_complex_ofReal]
        rfl
      _ = _ := by
        simp_rw [hexp]
        rw [integral_finset_sum _ (fun h _ => hint h)]
        simp_rw [integral_frequencySum_mul_conj]
        simp only [Complex.re_sum, Fintype.sum_prod_type, apply_ite Complex.re,
          map_one, mul_one, Complex.one_re, Complex.zero_re, hU]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro xy hxy
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro x hx
        congr 2
        simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
          iteratedFrequency_polynomial_eval coord (X ^ k) J (fun i => (h i : R)) (x : R)
  rw [hid]
  apply Finset.sum_le_sum
  intro xy hxy
  rw [iteratedDifferenceFiber_card_real]
  apply Finset.sum_le_sum
  intro h hh
  simp only [hcoord.eq_iff]
  rw [← Finset.sum_subtype (iteratedOverlap S J (fun i => (h i : R))) (fun _ => Iff.rfl)
    (fun x => if tuplePowerDifference k s S xy =
      (iteratedPolynomialDifference (X ^ k : R[X]) J (fun i => (h i : R))).eval x then (1 : ℝ) else 0)]
  have hf (x : R) :
      (if tuplePowerDifference k s S xy =
          (iteratedPolynomialDifference (X ^ k : R[X]) J (fun i => (h i : R))).eval x then (1 : ℝ) else 0) =
        (if (iteratedPolynomialDifference (X ^ k : R[X]) J (fun i => (h i : R))).eval x =
          tuplePowerDifference k s S xy then (1 : ℝ) else 0) := by
    exact if_congr eq_comm rfl rfl
  simp_rw [hf]
  exact Finset.sum_le_sum_of_subset_of_nonneg (iteratedOverlap_subset S J _)
    (fun x hx hnot => by split_ifs <;> norm_num)

theorem integral_power_even_eq_zero_tuples (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (S : Finset R) (k s : ℕ) :
    (∫ θ, ‖finiteFrequencySum S (fun x => coord (x ^ k)) θ‖ ^ (2 * s) ∂latticeHaar) =
      ((Finset.univ.filter (fun xy : (Fin s → S) × (Fin s → S) =>
        tuplePowerDifference k s S xy = 0)).card : ℝ) := by
  simp_rw [finiteFrequencySum_eq_frequencySum]
  rw [integral_norm_frequencySum_even]
  simp only [Finset.prod_const_one, map_one, mul_one, Complex.one_re]
  simp only [← map_sum, hcoord.eq_iff]
  simp [tuplePowerDifference, sub_eq_zero, Finset.sum_boole]

/-- The finite analytic induction step, with the zero and nonzero
arithmetic fibers visible.  Subsequent box/divisor estimates discharge
these finite numerical parameters. -/
theorem hua_induction_step (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (k J : ℕ) (hJ : 1 ≤ J)
    (Z M : ℝ) (hM : 0 ≤ M)
    (hz : ((iteratedDifferenceFiber S H k J 0).card : ℝ) ≤ Z)
    (hnz : ∀ xy : (Fin (2 ^ (J - 1)) → S) × (Fin (2 ^ (J - 1)) → S),
      tuplePowerDifference k (2 ^ (J - 1)) S xy ≠ 0 →
      ((iteratedDifferenceFiber S H k J (tuplePowerDifference k (2 ^ (J - 1)) S xy)).card : ℝ) ≤ M) :
    (∫ θ, ‖finiteFrequencySum S (fun x => coord (x ^ k)) θ‖ ^ (2 ^ (J + 1)) ∂latticeHaar) ≤
      (H.card : ℝ) ^ (2 ^ J - J - 1) *
        ((∫ θ, ‖finiteFrequencySum S (fun x => coord (x ^ k)) θ‖ ^ (2 ^ J) ∂latticeHaar) * Z +
          (S.card : ℝ) ^ (2 ^ J) * M) := by
  let v : R → ι → ℤ := fun x => coord (x ^ k)
  let s := 2 ^ (J - 1)
  have hs : 2 * s = 2 ^ J := by
    dsimp [s]
    rw [← pow_succ']
    congr 1
    omega
  have hi : Integrable (fun θ => ‖finiteFrequencySum S v θ‖ ^ (2 ^ (J + 1))) latticeHaar :=
    ((continuous_finiteFrequencySum S v).norm.pow _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun θ => (H.card : ℝ) ^ (2 ^ J - J - 1) *
      (‖finiteFrequencySum S v θ‖ ^ (2 ^ J) * (iteratedCubeSum S H J v θ).re)) latticeHaar :=
    (continuous_const.mul (((continuous_finiteFrequencySum S v).norm.pow _).mul
      (Complex.continuous_re.comp (continuous_iteratedCubeSum S H J v)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hreduce : (∫ θ, ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) *
        (iteratedCubeSum S H J v θ).re ∂latticeHaar) ≤
      ∑ xy : (Fin s → S) × (Fin s → S),
        ((iteratedDifferenceFiber S H k J (tuplePowerDifference k s S xy)).card : ℝ) := by
    simpa only [hs] using integral_even_mul_iteratedCube_le_fibers coord hcoord S H hH k s J hJ
  have hfibers : (∑ xy : (Fin s → S) × (Fin s → S),
      ((iteratedDifferenceFiber S H k J (tuplePowerDifference k s S xy)).card : ℝ)) ≤
      (∫ θ, ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) ∂latticeHaar) * Z +
        (S.card : ℝ) ^ (2 ^ J) * M := by
    calc
      _ ≤ ∑ xy : (Fin s → S) × (Fin s → S),
          ((if tuplePowerDifference k s S xy = 0 then Z else 0) + M) := by
        apply Finset.sum_le_sum
        intro xy hxy
        by_cases hzero : tuplePowerDifference k s S xy = 0
        · rw [hzero, if_pos rfl]
          linarith
        · rw [if_neg hzero, zero_add]
          exact hnz xy hzero
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin,
          Nat.cast_mul, Nat.cast_pow]
        rw [← integral_power_even_eq_zero_tuples coord hcoord, hs,
          ← pow_add, ← two_mul, hs]
  calc
    (∫ θ, ‖finiteFrequencySum S v θ‖ ^ (2 ^ (J + 1)) ∂latticeHaar) ≤
        ∫ θ, (H.card : ℝ) ^ (2 ^ J - J - 1) *
          (‖finiteFrequencySum S v θ‖ ^ (2 ^ J) * (iteratedCubeSum S H J v θ).re) ∂latticeHaar := by
      apply integral_mono hi hj
      intro θ
      have h := mul_le_mul_of_nonneg_left (finiteFrequencySum_pow_le_iteratedCube S H hH J hJ v θ)
        (show 0 ≤ ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) by positivity)
      calc
        _ = ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) * ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) := by
          rw [← pow_add, ← mul_two, ← pow_succ]
        _ ≤ _ := by nlinarith only [h]
    _ = (H.card : ℝ) ^ (2 ^ J - J - 1) *
        (∫ θ, ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) * (iteratedCubeSum S H J v θ).re ∂latticeHaar) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hreduce.trans hfibers) (by positivity)

#print axioms integral_even_mul_iteratedCube_le_fibers
#print axioms hua_induction_step

end WaringSiegel.WSL3
