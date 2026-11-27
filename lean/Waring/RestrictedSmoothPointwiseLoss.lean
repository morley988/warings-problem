import Waring.RestrictedSmoothShorterSums

/-! # Uniform subpower losses in the actual block reduction -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothFactorization
open SmoothMoments PrimeSupportedCount

theorem raise_subpower_bound (n : ℕ) {ε P C x : ℝ} (hε : 0 < ε)
    (hP : 1 ≤ P) (hC : 0 ≤ C) (hx0 : 0 ≤ x)
    (hx : x ≤ C*P^(ε/((n : ℝ)+1))) : x^n ≤ C^n*P^ε := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hδ : 0 < ε/((n : ℝ)+1) := div_pos hε (by positivity)
  have hpow : (ε/((n : ℝ)+1))*(n : ℝ) ≤ ε := by
    have hid : (ε/((n : ℝ)+1))*((n : ℝ)+1)=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  calc
    _ ≤ (C*P^(ε/((n : ℝ)+1)))^n := pow_le_pow_left₀ hx0 hx n
    _ = C^n*P^((ε/((n : ℝ)+1))*(n : ℝ)) := by
      rw [mul_pow,← Real.rpow_mul_natCast hPp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP hpow) (pow_nonneg hC _)

theorem supportedNumbers_mono {N M q : ℕ} (hNM : N ≤ M) :
    supportedNumbers N q ⊆ supportedNumbers M q := by
  classical
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn,hq⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hNM⟩,hq⟩

theorem supported_card_power_bound (n : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ q : ℕ,0 < q →
      (q : ℝ) ≤ P^B → ∀ X : ℝ,X ≤ P →
        ((supportedNumbers ⌊X⌋₊ q).card : ℝ)^n ≤ C*P^ε := by
  have hδ : 0 < ε/((n : ℝ)+1) := div_pos hε (by positivity)
  obtain ⟨D,hD,hb⟩ := supportedNumbers_polynomial_scale (A := 1) (by norm_num) hB hδ
  refine ⟨D^n,pow_pos hD _,?_⟩
  intro P hP q hq hqP X hXP
  apply raise_subpower_bound n hε hP hD.le (Nat.cast_nonneg _)
  have hc : ((supportedNumbers ⌊X⌋₊ q).card : ℝ) ≤
      ((supportedNumbers ⌊P⌋₊ q).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (supportedNumbers_mono (Nat.floor_mono hXP)))
  exact hc.trans (by simpa only [Real.rpow_one] using hb P hP q hq hqP)

theorem mixedPrimeWeyl_epsilon (k : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ q : ℕ,0 < q →
      (q : ℝ) ≤ P^B → ∀ X R : ℝ,0 ≤ X → X ≤ P → ∀ π : ℕ,(π : ℝ) ≤ R →
      ∀ α : ℝ, ‖mixedPrimeWeyl k q π X R α‖^s ≤
        C*P^ε*∑ z ∈ smoothNumbers X R,
          ‖smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*α)‖^s := by
  obtain ⟨C,hC,hbound⟩ := supported_card_power_bound (s-1) hB hε
  refine ⟨C,hC,?_⟩
  intro P hP q hq hqP X R hX hXP π hπR α
  apply (mixedPrimeWeyl_holder k q π hs hX hπR α).trans
  exact mul_le_mul_of_nonneg_right (hbound P hP q hq hqP X hXP)
    (Finset.sum_nonneg (fun _ _ => by positivity))

theorem smallCoprimeSum_power_bound (s : ℕ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ q : ℕ,0 < q →
      (q : ℝ) ≤ P^B → ∀ R M α : ℝ,0 ≤ M → ∀ k : ℕ,
        ‖smallCoprimeSum k q P R M α‖^s ≤ C*P^ε*M^s := by
  have hδ : 0 < ε/((s : ℝ)+1) := div_pos hε (by positivity)
  obtain ⟨D,hD,hb⟩ := smallCoprimeSum_bound hB hδ
  refine ⟨D^s,pow_pos hD _,?_⟩
  intro P hP q hq hqP R M α hM k
  calc
    _ ≤ (D*P^(ε/((s : ℝ)+1))*M)^s :=
      pow_le_pow_left₀ (norm_nonneg _) (hb P hP q hq hqP R M α hM k) s
    _ = (D*P^(ε/((s : ℝ)+1)))^s*M^s := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (raise_subpower_bound s hε hP hD.le (by positivity) le_rfl) (pow_nonneg hM _)

#print axioms mixedPrimeWeyl_epsilon
#print axioms smallCoprimeSum_power_bound
end Waring.RestrictedSmoothFactorization
