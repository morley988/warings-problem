import Waring.QuadraticModulation
import Waring.RationalHeightMin
import Waring.RationalHeightScale
import Waring.ReciprocalSums
import Mathlib.Data.Nat.Log

/-!
# Quadratic sums with intrinsic rational height

This file combines finite quadratic differencing, the proved reciprocal-sum
estimate, rational transference, and the factor-two comparison of intrinsic
heights. The linear modulation is arbitrary throughout.
-/

noncomputable section
open scoped BigOperators
namespace Waring.QuadraticHeight

@[simp] theorem integerDistance_neg (α : ℝ) : integerDistance (-α) = integerDistance α := by
  have h (x : ℝ) : integerDistance (-x) ≤ integerDistance x := by
    have hb := round_le (-x) (-round x)
    unfold integerDistance
    convert hb using 1
    simp only [Int.cast_neg, neg_sub_neg, abs_sub_comm]
  exact le_antisymm (h α) (by simpa only [neg_neg] using h (-α))

@[simp] theorem linearSumBound_neg (N : ℕ) (α : ℝ) :
    linearSumBound N (-α) = linearSumBound N α := by
  simp only [linearSumBound, integerDistance_neg]

/-- The two signs of the shift cost at most a factor of two; the zero shift
is included in both copies on the right. -/
theorem symmetric_sum_le_twice (m : ℕ) (f : ℤ → ℝ)
    (hf : ∀ u, 0 ≤ f u) (heven : ∀ u, f (-u) = f u) :
    (∑ u ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), f u) ≤
      2 * ∑ n ∈ Finset.range (m+1), f (n : ℤ) := by
  let s := (Finset.range (m+1)).image (fun n : ℕ => (n : ℤ))
  let t := (Finset.range (m+1)).image (fun n : ℕ => -(n : ℤ))
  have hsub : Finset.Icc (-(m : ℤ)) (m : ℤ) ⊆ s ∪ t := by
    intro u hu
    rcases Finset.mem_Icc.mp hu with ⟨hlo, hhi⟩
    by_cases hu0 : 0 ≤ u
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨u.toNat, Finset.mem_range.mpr (by omega), Int.toNat_of_nonneg hu0⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨(-u).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      exact neg_neg u
  have hs : (∑ u ∈ s, f u) = ∑ n ∈ Finset.range (m+1), f (n : ℤ) := by
    apply Finset.sum_image
    intro i _ j _ hij
    dsimp at hij
    exact_mod_cast hij
  have ht : (∑ u ∈ t, f u) = ∑ n ∈ Finset.range (m+1), f (n : ℤ) := by
    calc
      _ = ∑ n ∈ Finset.range (m+1), f (-(n : ℤ)) := by
        apply Finset.sum_image
        intro i _ j _ hij
        exact_mod_cast neg_injective hij
      _ = _ := by simp only [heven]
  calc
    _ ≤ ∑ u ∈ s ∪ t, f u :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hf u)
    _ ≤ (∑ u ∈ s, f u)+(∑ u ∈ t, f u) := by
      have hid := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
      have hnonneg : 0 ≤ ∑ u ∈ s ∩ t, f u := Finset.sum_nonneg (fun u _ => hf u)
      linarith
    _ = _ := by rw [hs, ht]; ring

/-- One-sided reciprocal majorant for any nonempty integer interval. -/
theorem quadratic_interval_one_sided_bound (a b : ℤ) (β t : ℝ) (hab : a ≤ b) :
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^2 ≤
      2 * ∑ n ∈ Finset.range (b+1-a).toNat,
        linearSumBound (b+1-a).toNat (2*β*(n : ℝ)) := by
  have h := symmetric_sum_le_twice (b-a).toNat
    (fun u => linearSumBound (b+1-a).toNat (2*β*(u : ℝ)))
    (fun u => QuadraticModulation.linearSumBound_nonneg _ _)
    (fun u => by simp only [Int.cast_neg, mul_neg, linearSumBound_neg])
  have hnat : (b-a).toNat+1 = (b+1-a).toNat := by omega
  have hcast : ((b-a).toNat : ℤ) = b-a := Int.toNat_of_nonneg (by omega)
  have hlo : -(b-a) = a-b := by omega
  rw [hnat, hcast, hlo] at h
  exact (QuadraticModulation.quadratic_interval_reciprocal_bound a b β t).trans
    (by simpa only [Int.cast_natCast] using h)

/-- Direct composition of quadratic differencing with the proved intrinsic
reciprocal-sum theorem. The conductor is the square of the interval length. -/
theorem quadratic_interval_double_phase_height_bound (a b : ℤ) (β t : ℝ) (T : ℕ)
    (hab : a ≤ b) (hNT : ((b+1-a).toNat : ℝ) ≤ 2^T) :
    let N : ℝ := (b+1-a).toNat
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^2 ≤
      256 * (N^2/RationalHeight.height (N^2) (2*β)+2*N+
        RationalHeight.height (N^2) (2*β)) * (T+1 : ℕ) := by
  have hN : 0 < (b+1-a).toNat := by omega
  have hb := ReciprocalSums.linearSumBound_sum_intrinsic (2*β)
    (b+1-a).toNat (b+1-a).toNat T hN hN hNT
  have hmul := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  have h := (quadratic_interval_one_sided_bound a b β t hab).trans hmul
  dsimp only
  simp only [pow_two] at h ⊢
  convert h using 1
  ring

/-- Uniform in arbitrary real modulation, with the height at the original
quadratic phase. All logarithmic loss is represented by the explicit dyadic
depth `T+1`, where the interval length is at most `2^T`. -/
theorem quadratic_interval_height_bound (a b : ℤ) (β t : ℝ) (T : ℕ)
    (hab : a ≤ b) (hNT : ((b+1-a).toNat : ℝ) ≤ 2^T) :
    let N : ℝ := (b+1-a).toNat
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^2 ≤
      768 * (N+N^2/RationalHeight.height (N^2) β) * (T+1 : ℕ) := by
  let N : ℝ := (b+1-a).toNat
  let B := RationalHeight.height (N^2) β
  let B₂ := RationalHeight.height (N^2) (2*β)
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ (b+1-a).toNat by omega)
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hV : 1 ≤ N^2 := by nlinarith
  have hB : 0 < B := RationalHeight.height_pos _ _
  have hB₂ : 0 < B₂ := RationalHeight.height_pos _ _
  have hBcompare : B ≤ 2*B₂ := by
    simpa only [Nat.cast_ofNat] using
      (RationalHeight.height_mul_phase_lower (α := β) (V := N^2)
        (sq_pos_of_pos hNpos) (h := 2) (by norm_num))
  have hB₂N : B₂ ≤ N := by
    have h := RationalHeight.height_le_sqrt hV (2*β)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hNpos] using h
  have hdiv : N^2/B₂ ≤ 2*(N^2/B) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hB₂ hB).mpr
    nlinarith [mul_le_mul_of_nonneg_left hBcompare (sq_nonneg N)]
  have hx : 0 ≤ N^2/B := div_nonneg (sq_nonneg N) hB.le
  have h := quadratic_interval_double_phase_height_bound a b β t T hab hNT
  change _ ≤ 256*(N^2/B₂+2*N+B₂)*(T+1 : ℕ) at h
  change _ ≤ 768*(N+N^2/B)*(T+1 : ℕ)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

/-- The pointwise fourth-power estimate Q1, with an explicit absolute
constant and squared dyadic logarithmic factor. No quadratic-height bound
appears among its hypotheses. -/
theorem quadratic_interval_fourth_height_bound (a b : ℤ) (β t : ℝ) (T : ℕ)
    (hab : a ≤ b) (hNT : ((b+1-a).toNat : ℝ) ≤ 2^T) :
    let N : ℝ := (b+1-a).toNat
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^4 ≤
      1179648 * (T+1 : ℕ)^2 *
        (N^2+N^4/(RationalHeight.height (N^2) β)^2) := by
  let N : ℝ := (b+1-a).toNat
  let B := RationalHeight.height (N^2) β
  let Z := ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖
  have hB : 0 < B := RationalHeight.height_pos _ _
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hT : (0 : ℝ) ≤ (T+1 : ℕ) := by positivity
  have h := quadratic_interval_height_bound a b β t T hab hNT
  change Z^2 ≤ 768*(N+N^2/B)*(T+1 : ℕ) at h
  have hs := pow_le_pow_left₀ (sq_nonneg Z) h 2
  have hsum : (N+N^2/B)^2 ≤ 2*(N^2+(N^2/B)^2) := by nlinarith [sq_nonneg (N-N^2/B)]
  have hfactor : (0 : ℝ) ≤ (768 : ℝ)^2*((T+1 : ℕ) : ℝ)^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsum hfactor
  have hdiv : (N^2/B)^2 = N^4/B^2 := by ring
  change Z^4 ≤ 1179648*(T+1 : ℕ)^2*(N^2+N^4/B^2)
  rw [hdiv] at hm
  nlinarith

/-- A canonical, explicit logarithmic version: the dyadic depth is the
ceiling of the binary logarithm of the positive interval length. -/
theorem quadratic_interval_fourth_height_log_bound (a b : ℤ) (β t : ℝ)
    (hab : a ≤ b) :
    let n : ℕ := (b+1-a).toNat
    let N : ℝ := n
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^4 ≤
      1179648 * (Nat.clog 2 n+1 : ℕ)^2 *
        (N^2+N^4/(RationalHeight.height (N^2) β)^2) := by
  apply quadratic_interval_fourth_height_bound a b β t (Nat.clog 2 (b+1-a).toNat) hab
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (b+1-a).toNat

/-- The square bound with a common real ambient length `P`, useful when
the interval changes between sampled phases. -/
theorem quadratic_interval_height_bound_ambient (a b : ℤ) (β t P : ℝ) (T : ℕ)
    (hab : a ≤ b) (hP : 1 ≤ P)
    (hNP : ((b+1-a).toNat : ℝ) ≤ P) (hPT : P ≤ 2^T) :
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^2 ≤
      768 * (P+P^2/RationalHeight.height (P^2) β) * (T+1 : ℕ) := by
  let N : ℝ := (b+1-a).toNat
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (show 0 < (b+1-a).toNat by omega)
  have hNP' : N ≤ P := hNP
  have hratio : N^2/RationalHeight.height (N^2) β ≤
      P^2/RationalHeight.height (P^2) β :=
    RationalHeight.conductor_div_height_mono (sq_pos_of_pos hN) (by nlinarith)
  have hb := quadratic_interval_height_bound a b β t T hab (hNP.trans hPT)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith

/-- Ambient-length Q1 with no premise asserting a quadratic exponential-sum
estimate. The logarithmic loss is explicit and uniform in `t`. -/
theorem quadratic_interval_fourth_height_bound_ambient (a b : ℤ) (β t P : ℝ) (T : ℕ)
    (hab : a ≤ b) (hP : 1 ≤ P)
    (hNP : ((b+1-a).toNat : ℝ) ≤ P) (hPT : P ≤ 2^T) :
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖^4 ≤
      1179648 * (T+1 : ℕ)^2 *
        (P^2+P^4/(RationalHeight.height (P^2) β)^2) := by
  let B := RationalHeight.height (P^2) β
  let Z := ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e (β*(z : ℝ)^2+t*z)‖
  have hB : 0 < B := RationalHeight.height_pos _ _
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have h := quadratic_interval_height_bound_ambient a b β t P T hab hP hNP hPT
  change Z^2 ≤ 768*(P+P^2/B)*(T+1 : ℕ) at h
  have hs := pow_le_pow_left₀ (sq_nonneg Z) h 2
  have hsum : (P+P^2/B)^2 ≤ 2*(P^2+(P^2/B)^2) := by nlinarith [sq_nonneg (P-P^2/B)]
  have hfactor : (0 : ℝ) ≤ (768 : ℝ)^2*((T+1 : ℕ) : ℝ)^2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hsum hfactor
  have hdiv : (P^2/B)^2 = P^4/B^2 := by ring
  change Z^4 ≤ 1179648*(T+1 : ℕ)^2*(P^2+P^4/B^2)
  rw [hdiv] at hm
  nlinarith

/-- A fixed positive integer leading coefficient costs only its square in
the explicit Q1 constant. The real linear modulation remains unrestricted. -/
theorem quadratic_interval_fourth_height_integer_coefficient
    (a b : ℤ) (β t P : ℝ) (c T : ℕ) (hc : 0 < c)
    (hab : a ≤ b) (hP : 1 ≤ P)
    (hNP : ((b+1-a).toNat : ℝ) ≤ P) (hPT : P ≤ 2^T) :
    ‖∑ z ∈ Finset.Icc a b, QuadraticModulation.e ((c : ℝ)*β*(z : ℝ)^2+t*z)‖^4 ≤
      1179648 * (c : ℝ)^2 * (T+1 : ℕ)^2 *
        (P^2+P^4/(RationalHeight.height (P^2) β)^2) := by
  let B := RationalHeight.height (P^2) β
  let Bc := RationalHeight.height (P^2) ((c : ℝ)*β)
  have hB : 0 < B := RationalHeight.height_pos _ _
  have hBc : 0 < Bc := RationalHeight.height_pos _ _
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hcompare : B ≤ (c : ℝ)*Bc :=
    RationalHeight.height_mul_phase_lower (sq_pos_of_pos hPpos) hc
  have hdiv : P^2/Bc ≤ (c : ℝ)*(P^2/B) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hBc hB).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcompare (sq_nonneg P)]
  have hs := pow_le_pow_left₀ (div_nonneg (sq_nonneg P) hBc.le) hdiv 2
  have hPfourth : (P^2/Bc)^2 = P^4/Bc^2 := by ring
  have hPfourth' : ((c : ℝ)*(P^2/B))^2 = (c : ℝ)^2*(P^4/B^2) := by ring
  rw [hPfourth, hPfourth'] at hs
  have hmain : P^2+P^4/Bc^2 ≤ (c : ℝ)^2*(P^2+P^4/B^2) := by
    have hc2 : (1 : ℝ) ≤ (c : ℝ)^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hc2 (sq_nonneg P)
    nlinarith
  have hb := quadratic_interval_fourth_height_bound_ambient a b ((c : ℝ)*β) t P T
    hab hP hNP hPT
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left hmain
    (show (0 : ℝ) ≤ 1179648*(T+1 : ℕ)^2 by positivity)
  convert hm using 1
  ring

#print axioms quadratic_interval_height_bound
#print axioms quadratic_interval_fourth_height_bound
#print axioms quadratic_interval_fourth_height_log_bound
#print axioms quadratic_interval_fourth_height_bound_ambient
#print axioms quadratic_interval_fourth_height_integer_coefficient

end Waring.QuadraticHeight
