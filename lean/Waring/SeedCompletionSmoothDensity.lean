import Waring.SmoothProductDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform smooth-number density at arbitrary real lengths

The already proved product-box count is extended from integer power scales
to every real length. Constants are uniform in the ambient scale and in
the shorter cutoff. This is the diagonal supply needed to absorb the bad
branch in successive efficient differencing.
-/

noncomputable section
namespace Waring.SmoothMoments

theorem half_le_floor_of_one_le {x : ℝ} (hx : 1 ≤ x) : x/2 ≤ (⌊x⌋₊ : ℝ) := by
  have hf : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hfR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hf
  have hx' := Nat.lt_floor_add_one x
  linarith

/-- A fixed positive smoothness power supplies almost linearly many
smooth integers, uniformly for every shorter real cutoff. -/
theorem smooth_card_lower_uniform {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ P Q : ℝ, 1 ≤ Q → Q ≤ P →
      c*Q^(1-ε) ≤ ((smoothNumbers Q (P^η)).card : ℝ) := by
  let L : ℕ := max 1 ⌈η⁻¹⌉₊
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hLη : 1 ≤ (L : ℝ)*η := by
    have hh : η⁻¹ ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈η⁻¹⌉₊)
    calc
      1 = η⁻¹*η := (inv_mul_cancel₀ hη.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hh hη.le
  let δ : ℝ := min ε (1/2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨c,hc,hprod⟩ := smooth_card_lower_product_scale L hδ
  refine ⟨c*((2 : ℝ)^L)⁻¹,by positivity,?_⟩
  intro P Q hQ hQP
  have hP : 1 ≤ P := hQ.trans hQP
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  let x : ℝ := Q^((L : ℝ)⁻¹)
  let M : ℕ := ⌊x⌋₊
  have hx : 1 ≤ x := Real.one_le_rpow hQ (by positivity)
  have hM : 1 ≤ M := Nat.le_floor (by simpa using hx)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (zero_lt_one.trans_le hM)
  have hMx : (M : ℝ) ≤ x := Nat.floor_le (zero_le_one.trans hx)
  have hxM : x/2 ≤ (M : ℝ) := half_le_floor_of_one_le hx
  have hxpow : x^L=Q := by
    dsimp [x]
    rw [← Real.rpow_mul_natCast hQp.le,inv_mul_cancel₀ hLR.ne',Real.rpow_one]
  have hMQ : (M : ℝ)^L ≤ Q := by
    rw [← hxpow]
    exact pow_le_pow_left₀ hMp.le hMx _
  have hQM : Q ≤ (2 : ℝ)^L*(M : ℝ)^L := by
    rw [← hxpow,← mul_pow]
    apply pow_le_pow_left₀ (zero_le_one.trans hx)
    linarith
  have hMR : (M : ℝ) ≤ P^η := by
    calc
      (M : ℝ) ≤ ((M : ℝ)^L)^η := product_scale_smoothness hM hLη
      _ ≤ P^η := Real.rpow_le_rpow (by positivity) (hMQ.trans hQP) hη.le
  have hsub : smoothNumbers ((M : ℝ)^L) M ⊆ smoothNumbers Q (P^η) :=
    (smoothNumbers_mono_length hMQ).trans (smoothNumbers_mono_cutoff hMR)
  have hcount : ((smoothNumbers ((M : ℝ)^L) M).card : ℝ) ≤
      ((smoothNumbers Q (P^η)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hpow : Q^(1-δ) ≤ (2 : ℝ)^L*((M : ℝ)^L)^(1-δ) := by
    calc
      Q^(1-δ) ≤ ((2 : ℝ)^L*(M : ℝ)^L)^(1-δ) :=
        Real.rpow_le_rpow hQp.le hQM (sub_nonneg.mpr hδ1)
      _ = ((2 : ℝ)^L)^(1-δ)*((M : ℝ)^L)^(1-δ) :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (2 : ℝ)^L*((M : ℝ)^L)^(1-δ) := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
          (show 1-δ ≤ 1 by linarith)).trans_eq (Real.rpow_one _)
  calc
    c*((2 : ℝ)^L)⁻¹*Q^(1-ε) ≤ c*((2 : ℝ)^L)⁻¹*Q^(1-δ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ
        (sub_le_sub_left (min_le_left ε (1/2 : ℝ)) 1)) (by positivity)
    _ ≤ c*((2 : ℝ)^L)⁻¹*((2 : ℝ)^L*((M : ℝ)^L)^(1-δ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = c*((M : ℝ)^L)^(1-δ) := by field_simp
    _ ≤ ((smoothNumbers ((M : ℝ)^L) M).card : ℝ) := hprod M hM
    _ ≤ _ := hcount

#print axioms smooth_card_lower_uniform

/-- The useful absorption form at a quotient length. The constant precedes
every ambient scale and every admissible quotient. -/
theorem short_smooth_card_absorption {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P Q M : ℝ, 1 ≤ M → M ≤ Q → Q ≤ P →
      Q ≤ C*M*P^ε*((smoothNumbers (Q/M) (P^η)).card : ℝ) := by
  obtain ⟨c,hc,hcount⟩ := smooth_card_lower_uniform hη hε
  refine ⟨max 1 c⁻¹,le_max_left _ _,?_⟩
  intro P Q M hM hMQ hQP
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hQp : 0 < Q := hMp.trans_le hMQ
  have hPp : 0 < P := hQp.trans_le hQP
  have hY : 1 ≤ Q/M := (one_le_div hMp).mpr hMQ
  have hYP : Q/M ≤ P := (div_le_self hQp.le hM).trans hQP
  have hypos : 0 < Q/M := div_pos hQp hMp
  have hd := hcount P (Q/M) hY hYP
  have hpow : (Q/M)^ε ≤ P^ε := Real.rpow_le_rpow hypos.le hYP hε.le
  have hmain : c*Q ≤ M*P^ε*((smoothNumbers (Q/M) (P^η)).card : ℝ) := by
    calc
      c*Q = M*(c*(Q/M)^(1-ε)*(Q/M)^ε) := by
        rw [mul_assoc c,← Real.rpow_add hypos,show 1-ε+ε=1 by ring,Real.rpow_one]
        field_simp
      _ ≤ M*(((smoothNumbers (Q/M) (P^η)).card : ℝ)*P^ε) := by
        gcongr
      _ = _ := by ring
  have hdivide : Q ≤ c⁻¹*(M*P^ε*((smoothNumbers (Q/M) (P^η)).card : ℝ)) := by
    apply (mul_le_mul_left hc).mp
    simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] using hmain
  calc
    Q ≤ c⁻¹*(M*P^ε*((smoothNumbers (Q/M) (P^η)).card : ℝ)) := hdivide
    _ ≤ max 1 c⁻¹*(M*P^ε*((smoothNumbers (Q/M) (P^η)).card : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    _ = _ := by ring

#print axioms short_smooth_card_absorption
end Waring.SmoothMoments
