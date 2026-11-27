import Waring.EndgameCompletionLocalFactors
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Actual Euler product and summable prime-power tail majorants -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace Waring.EndgameCompletion

theorem productSingularCoefficient_multiplicative (k u v L : ℕ) (n : ℤ)
    {q r : ℕ} (hqr : q.Coprime r) :
    productSingularCoefficient k u v L n (q*r)=
      productSingularCoefficient k u v L n q*productSingularCoefficient k u v L n r := by
  by_cases hq : q=0
  · subst q
    simp [productSingularCoefficient_zero]
  by_cases hr : r=0
  · subst r
    simp [productSingularCoefficient_zero]
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  exact productSingularCoefficient_coprime q r k u v L hqr n

theorem productSingularSeries_hasProd (k u v L : ℕ) (n : ℤ)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v L n q‖)) :
    HasProd (fun p : Nat.Primes=>productLocalFactor k u v L n p)
      (productSingularSeries k u v L n) := by
  exact EulerProduct.eulerProduct_hasProd (productSingularCoefficient_one k u v L n)
    (productSingularCoefficient_multiplicative k u v L n) hsum
    (productSingularCoefficient_zero k u v L n)

def primePowerEmbedding (x : Nat.Primes × ℕ) : ℕ := (x.1 : ℕ)^(x.2+1)

theorem primePowerEmbedding_injective : Function.Injective primePowerEmbedding := by
  rintro ⟨p,r⟩ ⟨q,s⟩ he
  have hh := p.prop.pow_inj q.prop he
  exact Prod.ext (Subtype.ext hh.1) hh.2

def primeTailMajorant (b : ℕ→ℝ) (p : Nat.Primes) : ℝ :=
  ∑' r : ℕ,b ((p : ℕ)^(r+1))

theorem primeTailMajorant_summable {b : ℕ→ℝ} (hb : Summable b) :
    Summable (primeTailMajorant b) := by
  exact (hb.comp_injective primePowerEmbedding_injective).prod

theorem primeTailMajorant_nonneg {b : ℕ→ℝ} (hb : ∀ q,0≤b q) (p : Nat.Primes) :
    0≤primeTailMajorant b p := tsum_nonneg (fun _=>hb _)

theorem productLocalFactor_sub_one (k u v L : ℕ) (n : ℤ) (p : Nat.Primes)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v L n q‖)) :
    productLocalFactor k u v L n p-1=
      ∑' r : ℕ,productSingularCoefficient k u v L n ((p : ℕ)^(r+1)) := by
  have hs := hsum.of_norm.comp_injective (Nat.pow_right_injective p.prop.one_lt)
  have he := hs.tsum_eq_zero_add
  simp only [Function.comp_apply,pow_zero,productSingularCoefficient_one] at he
  rw [productLocalFactor,he]
  ring

theorem productLocalFactor_sub_one_norm_le (k u v L : ℕ) (n : ℤ)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v L n q‖))
    {b : ℕ→ℝ} (hb : Summable b)
    (hbound : ∀ q,‖productSingularCoefficient k u v L n q‖≤b q) (p : Nat.Primes) :
    ‖productLocalFactor k u v L n p-1‖≤primeTailMajorant b p := by
  have hinj : Function.Injective (fun r : ℕ=>(p : ℕ)^(r+1)) :=
    (Nat.pow_right_injective p.prop.one_lt).comp (fun _ _ h=>Nat.add_right_cancel h)
  have hs : Summable (fun r : ℕ=>‖productSingularCoefficient k u v L n ((p : ℕ)^(r+1))‖) :=
    hsum.comp_injective hinj
  rw [productLocalFactor_sub_one k u v L n p hsum]
  exact (norm_tsum_le_tsum_norm hs).trans
    (tsum_le_tsum (fun r=>hbound _) hs (hb.comp_injective hinj))

theorem degree8_localFactor_tail_majorant (L : ℕ) :
    ∃ b : Nat.Primes→ℝ,Summable b ∧ (∀ p,0≤b p) ∧
      ∀ n : ℤ,∀ p : Nat.Primes,‖productLocalFactor 8 8 30 (L+1) n p-1‖≤b p := by
  obtain ⟨C,hC,hbound⟩ := degree8_productSingularCoefficient_bound L
  let B : ℕ→ℝ := fun q=>C*(q : ℝ)^(-2 : ℝ)
  have hB : Summable B :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left C
  refine ⟨primeTailMajorant B,primeTailMajorant_summable hB,
    primeTailMajorant_nonneg (fun q=>by dsimp [B]; positivity),?_⟩
  intro n p
  exact productLocalFactor_sub_one_norm_le 8 8 30 (L+1) n
    (degree8_productSingularCoefficient_summable L n) hB (hbound n) p

theorem degree9_localFactor_tail_majorant (L : ℕ) :
    ∃ b : Nat.Primes→ℝ,Summable b ∧ (∀ p,0≤b p) ∧
      ∀ n : ℤ,∀ p : Nat.Primes,‖productLocalFactor 9 11 35 (L+1) n p-1‖≤b p := by
  obtain ⟨C,hC,hbound⟩ := degree9_productSingularCoefficient_bound L
  let B : ℕ→ℝ := fun q=>C*(q : ℝ)^(-2 : ℝ)
  have hB : Summable B :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ)< -1)).mul_left C
  refine ⟨primeTailMajorant B,primeTailMajorant_summable hB,
    primeTailMajorant_nonneg (fun q=>by dsimp [B]; positivity),?_⟩
  intro n p
  exact productLocalFactor_sub_one_norm_le 9 11 35 (L+1) n
    (degree9_productSingularCoefficient_summable L n) hB (hbound n) p

#print axioms productSingularSeries_hasProd
#print axioms primeTailMajorant_summable
#print axioms degree8_localFactor_tail_majorant
end Waring.EndgameCompletion
