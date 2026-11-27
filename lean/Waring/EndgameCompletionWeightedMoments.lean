import Waring.EndgameCompletionStrongMoments
import Waring.FourierCompletion

/-!
# Nonnegative weighted moments and the actual unweighted count

A coefficient bound controls each term in the exact even-moment expansion.
This is a coefficient/count comparison, not a pointwise comparison between
exponential sums.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion

def weightedFrequencySum {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) (t : ℝ) : ℂ :=
  ∑ i∈A,(w i : ℂ)*fourier (a i) (t : AddCircle (1 : ℝ))

def weightedFrequencyMoment {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) (r : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1,‖weightedFrequencySum A a w t‖^(2*r)

theorem continuous_weightedFrequencySum {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) : Continuous (weightedFrequencySum A a w) :=
  continuous_finset_sum A (fun i _=>continuous_const.mul
    ((fourier (a i)).continuous.comp (AddCircle.continuous_mk' 1)))

theorem weightedFrequencySum_pow {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) (r : ℕ) (t : ℝ) :
    weightedFrequencySum A a w t^r=
      weightedFrequencySum (finiteTuples A r) (fun x=>∑ i,a (x i))
        (fun x=>∏ i,w (x i)) t := by
  unfold weightedFrequencySum
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib,← Complex.ofReal_prod,
    prod_fourier_character]

theorem weightedFrequencySum_gram {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) :
    (∫ t in (0 : ℝ)..1,‖weightedFrequencySum A a w t‖^2)=
      ∑ p∈A×ˢA,if a p.1=a p.2 then w p.1*w p.2 else 0 := by
  classical
  have hpoint (t : ℝ) : ((‖weightedFrequencySum A a w t‖^2 : ℝ) : ℂ)=
      ∑ p∈A×ˢA,((w p.1*w p.2 : ℝ) : ℂ)*
        fourier (a p.1-a p.2) (t : AddCircle (1 : ℝ)) := by
    rw [Complex.ofReal_pow,← Complex.mul_conj']
    simp only [weightedFrequencySum,map_sum,map_mul,Complex.conj_ofReal,
      ← fourier_neg,Finset.sum_mul_sum,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [sub_eq_add_neg,fourier_add,Complex.ofReal_mul]
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal,Complex.ofReal_sum]
  simp_rw [hpoint]
  have hi (p : ι×ι) : IntervalIntegrable (fun t : ℝ=>((w p.1*w p.2 : ℝ) : ℂ)*
      fourier (a p.1-a p.2) (t : AddCircle (1 : ℝ))) volume 0 1 :=
    (continuous_const.mul ((fourier (a p.1-a p.2)).continuous.comp
      (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finset_sum (fun p _=>hi p)]
  apply Finset.sum_congr rfl
  intro p _
  rw [intervalIntegral.integral_const_mul,FourierCompletion.interval_integral_character]
  simp only [sub_eq_zero]
  split_ifs <;> simp

theorem weightedFrequencyMoment_expansion {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) (r : ℕ) :
    weightedFrequencyMoment A a w r=
      ∑ p∈equalSumPairs A a r,(∏ i,w (p.1 i))*(∏ i,w (p.2 i)) := by
  classical
  have he (t : ℝ) : ‖weightedFrequencySum A a w t‖^(2*r)=
      ‖weightedFrequencySum (finiteTuples A r) (fun x=>∑ i,a (x i))
        (fun x=>∏ i,w (x i)) t‖^2 := by
    rw [← weightedFrequencySum_pow,norm_pow,← pow_mul,Nat.mul_comm r 2]
  unfold weightedFrequencyMoment
  simp_rw [he]
  rw [weightedFrequencySum_gram]
  simp only [equalSumPairs,Finset.sum_filter]

theorem weightedFrequencyMoment_le {ι : Type*} (A : Finset ι) (a : ι→ℤ)
    (w : ι→ℝ) (r : ℕ) {K : ℝ} (hK : 0≤K)
    (hw0 : ∀ i∈A,0≤w i) (hwK : ∀ i∈A,w i≤K) :
    weightedFrequencyMoment A a w r≤K^(2*r)*frequencyEvenMoment A a r := by
  classical
  rw [weightedFrequencyMoment_expansion,frequencyEvenMoment_eq_card]
  have hprod {x : Fin r→ι} (hx : x∈finiteTuples A r) :
      0≤∏ i,w (x i) ∧ (∏ i,w (x i))≤K^r := by
    have hxi := Fintype.mem_piFinset.mp hx
    constructor
    · exact Finset.prod_nonneg (fun i _=>hw0 _ (hxi i))
    · simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        Finset.prod_le_prod (s := Finset.univ)
          (fun i _=>hw0 _ (hxi i)) (fun i _=>hwK _ (hxi i))
  calc
    _ ≤ ∑ _p∈equalSumPairs A a r,K^(2*r) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have h1 := hprod hp'.1
      have h2 := hprod hp'.2
      exact (mul_le_mul h1.2 h2.2 h2.1 (pow_nonneg hK r)).trans_eq
        (by rw [← pow_add,show r+r=2*r by omega])
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

#print axioms weightedFrequencyMoment_expansion
#print axioms weightedFrequencyMoment_le
end Waring.EndgameCompletion
