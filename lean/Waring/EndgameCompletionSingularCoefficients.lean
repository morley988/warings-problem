import Waring.EndgameCompletionProductCompleteSums

/-!
# Actual mixed product singular coefficients and absolute convergence

All bounds are uniform in the represented integer. Primitive complete sums
for both the ordinary and product variables have already been proved.
-/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

def ordinaryCompleteMean (q k : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  completeMonomialSumMod q k a/(q : ℂ)

def productCompleteMean (q k L : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  productCompleteSum q k L a/(q : ℂ)^L

theorem norm_ordinaryCompleteMean (q k : ℕ) [NeZero q] (a : ZMod q) :
    ‖ordinaryCompleteMean q k a‖=normalizedCompleteSum q k a := by
  simp only [ordinaryCompleteMean,normalizedCompleteSum,norm_div,Complex.norm_natCast]

theorem norm_productCompleteMean (q k L : ℕ) [NeZero q] (a : ZMod q) :
    ‖productCompleteMean q k L a‖=normalizedProductCompleteSum q k L a := by
  simp only [productCompleteMean,normalizedProductCompleteSum,norm_div,norm_pow,Complex.norm_natCast]

def productSingularCoefficient (k u v L : ℕ) (n : ℤ) (q : ℕ) : ℂ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ a : (ZMod q)ˣ,ordinaryCompleteMean q k a^u*productCompleteMean q k L a^v*
      ZMod.stdAddChar (-(a : ZMod q)*(n : ZMod q))

theorem productSingularCoefficient_zero (k u v L : ℕ) (n : ℤ) :
    productSingularCoefficient k u v L n 0=0 := by simp [productSingularCoefficient]

theorem productSingularCoefficient_nezero (k u v L q : ℕ) [NeZero q] (n : ℤ) :
    productSingularCoefficient k u v L n q=
      ∑ a : (ZMod q)ˣ,ordinaryCompleteMean q k a^u*productCompleteMean q k L a^v*
        ZMod.stdAddChar (-(a : ZMod q)*(n : ZMod q)) := by
  rw [productSingularCoefficient,dif_neg (NeZero.ne q)]

theorem productSingularCoefficient_norm_le (k u v L q : ℕ) [NeZero q] (n : ℤ)
    {A B e : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hS : ∀ a : (ZMod q)ˣ,normalizedCompleteSum q k a≤A*(q : ℝ)^e)
    (hT : ∀ a : (ZMod q)ˣ,normalizedProductCompleteSum q k L a≤B*(q : ℝ)^e) :
    ‖productSingularCoefficient k u v L n q‖≤(A^u*B^v)*(q : ℝ)^(1+e*(u+v : ℕ)) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hcard : Fintype.card (ZMod q)ˣ≤q := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun a : (ZMod q)ˣ=>(a : ZMod q)) Units.val_injective
  rw [productSingularCoefficient_nezero]
  calc
    _ ≤ ∑ a : (ZMod q)ˣ,‖ordinaryCompleteMean q k a^u*productCompleteMean q k L a^v*
        ZMod.stdAddChar (-(a : ZMod q)*(n : ZMod q))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ,(A*(q : ℝ)^e)^u*(B*(q : ℝ)^e)^v := by
      apply Finset.sum_le_sum
      intro a _
      simp only [norm_mul,norm_pow,norm_ordinaryCompleteMean,norm_productCompleteMean]
      have hc : ‖ZMod.stdAddChar (-(a : ZMod q)*(n : ZMod q))‖=1 := by
        simp [ZMod.stdAddChar_apply]
      rw [hc,mul_one]
      exact mul_le_mul (pow_le_pow_left₀ (normalizedCompleteSum_nonneg ..) (hS a) u)
        (pow_le_pow_left₀ (normalizedProductCompleteSum_nonneg ..) (hT a) v)
        (pow_nonneg (normalizedProductCompleteSum_nonneg ..) _) (by positivity)
    _ = (Fintype.card (ZMod q)ˣ : ℝ)*((A*(q : ℝ)^e)^u*(B*(q : ℝ)^e)^v) := by simp
    _ ≤ (q : ℝ)*((A*(q : ℝ)^e)^u*(B*(q : ℝ)^e)^v) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_pow,← Real.rpow_mul_natCast hq.le,← Real.rpow_mul_natCast hq.le]
      rw [show (q : ℝ)*(A^u*(q : ℝ)^(e*u)*(B^v*(q : ℝ)^(e*v)))=
        (A^u*B^v)*((q : ℝ)^(1 : ℝ)*((q : ℝ)^(e*u)*(q : ℝ)^(e*v))) by rw [Real.rpow_one]; ring,
        ← Real.rpow_add hq,← Real.rpow_add hq]
      congr 2
      push_cast
      ring

/-- A fixed summable majorant, uniform in n, for degree-eight product
singular coefficients. The constant may depend on the fixed product rank. -/
theorem degree8_productSingularCoefficient_bound (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℤ,∀ q : ℕ,
      ‖productSingularCoefficient 8 8 30 (L+1) n q‖≤C*(q : ℝ)^(-2 : ℝ) := by
  obtain ⟨A,hA,hS⟩ := degree8_normalizedCompleteSum_pointwise (ε := 1/32) (by norm_num)
  obtain ⟨B,hB,hT⟩ := degree8_productCompleteSum_pointwise L (ε := 1/32) (by norm_num)
  refine ⟨A^8*B^30,by positivity,?_⟩
  intro n q
  by_cases hq : q=0
  · subst q
    simp [productSingularCoefficient_zero,Real.zero_rpow (by norm_num : (-2 : ℝ)≠0)]
  letI : NeZero q := ⟨hq⟩
  have hb := productSingularCoefficient_norm_le 8 8 30 (L+1) q n hA.le hB.le (hS q) (hT q)
  norm_num at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (NeZero.pos q)) (by norm_num)) (by positivity))

theorem degree9_productSingularCoefficient_bound (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℤ,∀ q : ℕ,
      ‖productSingularCoefficient 9 11 35 (L+1) n q‖≤C*(q : ℝ)^(-2 : ℝ) := by
  obtain ⟨A,hA,hS⟩ := degree9_normalizedCompleteSum_pointwise (ε := 1/36) (by norm_num)
  obtain ⟨B,hB,hT⟩ := degree9_productCompleteSum_pointwise L (ε := 1/36) (by norm_num)
  refine ⟨A^11*B^35,by positivity,?_⟩
  intro n q
  by_cases hq : q=0
  · subst q
    simp [productSingularCoefficient_zero,Real.zero_rpow (by norm_num : (-2 : ℝ)≠0)]
  letI : NeZero q := ⟨hq⟩
  have hb := productSingularCoefficient_norm_le 9 11 35 (L+1) q n hA.le hB.le (hS q) (hT q)
  norm_num at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (NeZero.pos q)) (by norm_num)) (by positivity))

theorem degree8_productSingularCoefficient_summable (L : ℕ) (n : ℤ) :
    Summable (fun q=>‖productSingularCoefficient 8 8 30 (L+1) n q‖) := by
  obtain ⟨C,_,hb⟩ := degree8_productSingularCoefficient_bound L
  exact Summable.of_nonneg_of_le (fun q=>norm_nonneg _) (hb n)
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left C)

theorem degree9_productSingularCoefficient_summable (L : ℕ) (n : ℤ) :
    Summable (fun q=>‖productSingularCoefficient 9 11 35 (L+1) n q‖) := by
  obtain ⟨C,_,hb⟩ := degree9_productSingularCoefficient_bound L
  exact Summable.of_nonneg_of_le (fun q=>norm_nonneg _) (hb n)
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left C)

def productSingularSeries (k u v L : ℕ) (n : ℤ) : ℂ :=
  ∑' q : ℕ,productSingularCoefficient k u v L n q

#print axioms degree8_productSingularCoefficient_bound
#print axioms degree9_productSingularCoefficient_summable
end Waring.EndgameCompletion
