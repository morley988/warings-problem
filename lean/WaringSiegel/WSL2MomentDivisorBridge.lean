import WaringSiegel.WSL2MomentFourth
import WaringSiegel.WSL2IdealDivisors
import WaringSiegel.WSL2UnitGenerators

/-!
# Divisors in an archimedean box

This file connects the finite divisor parameter in the literal fourth moment
to ideal divisors and associated generators.  The norm controls are proved
for the actual infinite places of the number field.
-/

noncomputable section
open scoped NumberField BigOperators Classical

namespace WaringSiegel.WSL2

variable {K : Type*} [Field K] [NumberField K]

/-- Group a finite set of elements by the principal ideals they generate. -/
theorem finite_card_le_principal_ideal_card_mul (T : Finset (𝓞 K))
    (G : ℝ) (hG : 0 ≤ G)
    (hgen : ∀ a ∈ T, ((T.filter (fun h => Associated h a)).card : ℝ) ≤ G) :
    (T.card : ℝ) ≤ ((T.image (fun h => Ideal.span ({h} : Set (𝓞 K)))).card : ℝ) * G := by
  let f : 𝓞 K → Ideal (𝓞 K) := fun h => Ideal.span ({h} : Set (𝓞 K))
  have heq := Finset.card_eq_sum_card_fiberwise (s := T) (t := T.image f)
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hcast : (T.card : ℝ) = ∑ J ∈ T.image f,
      ((T.filter (fun h => f h = J)).card : ℝ) := by exact_mod_cast heq
  rw [hcast]
  calc
    (∑ J ∈ T.image f, ((T.filter (fun h => f h = J)).card : ℝ)) ≤
        ∑ _J ∈ T.image f, G := by
      apply Finset.sum_le_sum
      intro J hJ
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hJ
      simpa only [f, Ideal.span_singleton_eq_span_singleton] using hgen a ha
    _ = ((T.image f).card : ℝ) * G := by simp

/-- The ideal-divisor epsilon estimate applies to the principal-ideal image. -/
theorem principal_ideal_divisor_image_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : 𝓞 K, a ≠ 0 → ∀ T : Finset (𝓞 K),
      (∀ h ∈ T, h ∣ a) →
      ((T.image (fun h => Ideal.span ({h} : Set (𝓞 K)))).card : ℝ) ≤
        C * (absNorm a) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := IdealDivisorBounds.ideal_divisor_finset_bound (K := K) hε
  refine ⟨C, hC, ?_⟩
  intro a ha T hT
  have hA : Ideal.span ({a} : Set (𝓞 K)) ≠ 0 := by
    intro hz
    apply ha
    exact Ideal.span_singleton_eq_bot.mp hz
  have h := hbound (Ideal.span ({a} : Set (𝓞 K))) hA
    (T.image (fun h => Ideal.span ({h} : Set (𝓞 K)))) (by
      intro J hJ
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hJ
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr (hT b hb)))
  simpa only [Ideal.absNorm_span_singleton, Int.cast_natAbs, Int.cast_abs, absNorm] using h

/-- Bound the actual norm from bounds at every infinite place. -/
theorem absNorm_le_box {a : 𝓞 K} {L : ℝ} (hL : 0 ≤ L)
    (ha : ∀ v : NumberField.InfinitePlace K, v (a : K) ≤ L) :
    absNorm a ≤ L ^ Module.finrank ℚ K := by
  rw [← fieldAbsNorm_integer]
  have heq : fieldAbsNorm (a : K) =
      ∏ v : NumberField.InfinitePlace K, v (a : K) ^ v.mult := by
    simpa only [fieldAbsNorm, Rat.cast_abs] using
      (NumberField.InfinitePlace.prod_eq_abs_norm (a : K)).symm
  rw [heq, ← NumberField.InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod
  · intro v hv
    exact pow_nonneg (apply_nonneg v _) _
  · intro v hv
    exact pow_le_pow_left₀ (apply_nonneg v _) (ha v) _

theorem place_sub_le_twice {x y : 𝓞 K} {P : ℝ}
    (hx : ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (hy : ∀ v : NumberField.InfinitePlace K, v (y : K) ≤ P)
    (v : NumberField.InfinitePlace K) : v ((x - y : 𝓞 K) : K) ≤ 2 * P := by
  change v ((x : K) - (y : K)) ≤ 2 * P
  have hb := v.val.sub_le_add (x : K) (y : K)
  change v ((x : K) - (y : K)) ≤ v (x : K) + v (y : K) at hb
  exact hb.trans (by linarith [hx v, hy v])

theorem place_power_sub_le_twice {x y : 𝓞 K} {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (hy : ∀ v : NumberField.InfinitePlace K, v (y : K) ≤ P)
    (k : ℕ) (v : NumberField.InfinitePlace K) :
    v ((x ^ k - y ^ k : 𝓞 K) : K) ≤ 2 * P ^ k := by
  apply place_sub_le_twice
  · intro w
    change w ((x : K) ^ k) ≤ P ^ k
    rw [map_pow]
    exact pow_le_pow_left₀ (apply_nonneg w _) (hx w) _
  · intro w
    change w ((y : K) ^ k) ≤ P ^ k
    rw [map_pow]
    exact pow_le_pow_left₀ (apply_nonneg w _) (hy w) _

theorem powerDifferenceDivisors_place_bound (S : Finset (𝓞 K)) {P : ℝ}
    (hS : ∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (a h : 𝓞 K) (hh : h ∈ powerDifferenceDivisors S a)
    (v : NumberField.InfinitePlace K) : v (h : K) ≤ 2 * P := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hh).1
  exact place_sub_le_twice (hS p.1 (Finset.mem_product.mp hp).1)
    (hS p.2 (Finset.mem_product.mp hp).2) v

theorem powerDifference_norm_le {x y : 𝓞 K} {P : ℝ} (hP : 0 ≤ P)
    (hx : ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (hy : ∀ v : NumberField.InfinitePlace K, v (y : K) ≤ P) (k : ℕ) :
    absNorm (x ^ k - y ^ k) ≤ (2 * P ^ k) ^ Module.finrank ℚ K :=
  absNorm_le_box (by positivity) (place_power_sub_le_twice hP hx hy k)

/-- A uniform bound for actual element divisors lying in an archimedean box. -/
theorem ring_divisor_box_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ a : 𝓞 K, a ≠ 0 →
      ∀ T : Finset (𝓞 K), (∀ h ∈ T, h ∣ a) →
      (∀ h ∈ T, ∀ v : NumberField.InfinitePlace K, v (h : K) ≤ L) →
      (T.card : ℝ) ≤ C * (absNorm a) ^ ε *
        (1 + Real.log L) ^ NumberField.Units.rank K := by
  obtain ⟨A, hA, hideal⟩ := principal_ideal_divisor_image_bound (K := K) hε
  obtain ⟨B, hB, hgen⟩ := exists_associated_box_count_constant K
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro L hL a ha T hdiv hbox
  have hlog : 0 ≤ 1 + Real.log L := by linarith [Real.log_nonneg hL]
  have hG : 0 ≤ B * (1 + Real.log L) ^ NumberField.Units.rank K := by positivity
  have hfiber (b : 𝓞 K) (hb : b ∈ T) :
      ((T.filter (fun h => Associated h b)).card : ℝ) ≤
        B * (1 + Real.log L) ^ NumberField.Units.rank K := by
    apply hgen L hL T hbox b
    intro hz
    have hh := hdiv b hb
    rw [hz, zero_dvd_iff] at hh
    exact ha hh
  calc
    (T.card : ℝ) ≤ ((T.image (fun h => Ideal.span ({h} : Set (𝓞 K)))).card : ℝ) *
        (B * (1 + Real.log L) ^ NumberField.Units.rank K) :=
      finite_card_le_principal_ideal_card_mul T _ hG hfiber
    _ ≤ (A * absNorm a ^ ε) * (B * (1 + Real.log L) ^ NumberField.Units.rank K) :=
      mul_le_mul_of_nonneg_right (hideal a ha T hdiv) hG
    _ = _ := by ring

/-- The finite divisor parameter now has the required uniform arithmetic bound. -/
theorem powerDifferenceDivisors_card_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ S : Finset (𝓞 K),
      (∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      ∀ x ∈ S, ∀ y ∈ S, ∀ k : ℕ, x ^ k - y ^ k ≠ 0 →
      ((powerDifferenceDivisors S (x ^ k - y ^ k)).card : ℝ) ≤
        C * ((2 * P ^ k) ^ Module.finrank ℚ K : ℝ) ^ ε *
          (1 + Real.log (2 * P)) ^ NumberField.Units.rank K := by
  obtain ⟨C, hC, hbound⟩ := ring_divisor_box_bound (K := K) hε
  refine ⟨C, hC, ?_⟩
  intro P hP S hS x hx y hy k ha
  have hP0 : 0 ≤ P := by linarith
  have hlog : 0 ≤ 1 + Real.log (2 * P) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * P by linarith)]
  have h := hbound (2 * P) (by linarith) (x ^ k - y ^ k) ha
    (powerDifferenceDivisors S (x ^ k - y ^ k))
    (fun h hh => (Finset.mem_filter.mp hh).2.2)
    (fun h hh v => powerDifferenceDivisors_place_bound S hS _ h hh v)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (absNorm_nonneg _) (powerDifference_norm_le hP0 (hS x hx) (hS y hy) k)
        hε.le) hC.le) (by positivity))

end WaringSiegel.WSL2
