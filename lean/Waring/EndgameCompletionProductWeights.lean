import Waring.EndgameCompletionWeightedMoments
import Waring.SmoothProductDensity

/-!
# Product-box smooth weights

The labelled product box has exactly M^L elements, all of whose products
belong to the actual M-smooth set at scale P=M^L. Its weight multiplicities
have arbitrarily small power growth by the proved divisor estimate.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.EndgameCompletion
open SmoothMoments ProductMultiplicity

def productBox (L M : ℕ) : Finset (Fin L→ℕ) := finiteTuples (Finset.Icc 1 M) L

def productWeight (L M n : ℕ) : ℕ := (productFiber (productBox L M) n).card

def productWeyl (k L M : ℕ) (α : ℝ) : ℂ :=
  ∑ x∈productBox L M,phase k (tupleProduct x) α

def productMoment (k p L M : ℕ) : ℝ :=
  ∫ α in (0 : ℝ)..1,‖productWeyl k L M α‖^p

theorem productBox_card (L M : ℕ) : (productBox L M).card=M^L := by
  simp [productBox,finiteTuples,Fintype.card_piFinset]

theorem continuous_productWeyl (k L M : ℕ) : Continuous (productWeyl k L M) :=
  continuous_finset_sum _ (fun x _=>continuous_phase k (tupleProduct x))

theorem productWeyl_periodic (k L M : ℕ) : Function.Periodic (productWeyl k L M) 1 := by
  intro α
  unfold productWeyl
  apply Finset.sum_congr rfl
  intro x _
  exact RestrictedSmoothArcs.periodic_phase k (tupleProduct x) α

theorem norm_productWeyl_le (k L M : ℕ) (α : ℝ) : ‖productWeyl k L M α‖≤(M : ℝ)^L := by
  calc
    _ ≤ ∑ x∈productBox L M,‖phase k (tupleProduct x) α‖ := norm_sum_le _ _
    _ = _ := by simp [productBox_card]

theorem productMoment_nonneg (k p L M : ℕ) : 0≤productMoment k p L M :=
  intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _=>pow_nonneg (norm_nonneg _) p)

theorem productWeyl_regroup_smooth (k L M : ℕ) (hM : 1≤M) (α : ℝ) :
    productWeyl k L M α=
      ∑ n∈smoothNumbers ((M : ℝ)^L) M,(productWeight L M n : ℂ)*phase k n α := by
  classical
  have hmap : ∀ x∈productBox L M,tupleProduct x∈smoothNumbers ((M : ℝ)^L) M :=
    fun x hx=>product_box_mem_smooth L M hM hx
  rw [productWeyl,← Finset.sum_fiberwise_of_maps_to' hmap (fun n=>phase k n α)]
  simp only [productWeight,productFiber,Finset.sum_const,nsmul_eq_mul]

theorem productWeyl_regroup_ordinary (k L M : ℕ) (hM : 1≤M) (α : ℝ) :
    productWeyl k L M α=
      ∑ n∈Finset.Icc 1 (M^L),(productWeight L M n : ℂ)*phase k n α := by
  classical
  have hmap : ∀ x∈productBox L M,tupleProduct x∈Finset.Icc 1 (M^L) := by
    intro x hx
    have hh := (mem_smoothNumbers.mp (product_box_mem_smooth L M hM hx)).1
    simpa only [← Nat.cast_pow,Nat.floor_natCast,Finset.mem_Icc] using hh
  rw [productWeyl,← Finset.sum_fiberwise_of_maps_to' hmap (fun n=>phase k n α)]
  simp only [productWeight,productFiber,Finset.sum_const,nsmul_eq_mul]

theorem productWeyl_eq_weightedFrequencySum (k L M : ℕ) (hM : 1≤M) :
    productWeyl k L M=weightedFrequencySum (smoothNumbers ((M : ℝ)^L) M)
      (fun n=>((n^k : ℕ) : ℤ)) (fun n=>(productWeight L M n : ℝ)) := by
  funext α
  rw [productWeyl_regroup_smooth k L M hM α]
  simp only [weightedFrequencySum,phase_eq_fourier,Complex.ofReal_natCast]

theorem productWeight_le_rpow (L : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ M : ℕ,1≤M → ∀ n∈smoothNumbers ((M : ℝ)^L) M,
      (productWeight L M n : ℝ)≤C*((M : ℝ)^L)^ε := by
  obtain ⟨C,hC,h⟩ := productFiber_card_le_rpow L hε
  refine ⟨C,hC,?_⟩
  intro M _ n hn
  obtain ⟨⟨hn1,hnP⟩,_⟩ := mem_smoothNumbers.mp hn
  have hnr : (n : ℝ)≤(M : ℝ)^L :=
    (Nat.le_floor_iff (by positivity)).mp hnP
  exact (h (productBox L M) n hn1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hnr hε.le) hC.le)

/-- Actual product-weight even moments inherit the actual smooth moment,
with an arbitrarily small total power loss. The constant is uniform in k,M. -/
theorem productMoment_even_le_smooth (L r : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ k M : ℕ,1≤M →
      productMoment k (2*r) L M≤C*((M : ℝ)^L)^ε*
        smoothMoment k (2*r) ((M : ℝ)^L) M := by
  let δ := ε/(2*(r : ℝ)+1)
  have hrpos : 0<2*(r : ℝ)+1 := by positivity
  have hδ : 0<δ := div_pos hε hrpos
  obtain ⟨C,hC,hw⟩ := productWeight_le_rpow L hδ
  refine ⟨C^(2*r),by positivity,?_⟩
  intro k M hM
  have hp1 : 1≤(M : ℝ)^L := one_le_pow₀ (by exact_mod_cast hM)
  have hp : 0<(M : ℝ)^L := zero_lt_one.trans_le hp1
  have he : δ*(2*r : ℕ)≤ε := by
    have hid : δ*(2*(r : ℝ)+1)=ε := div_mul_cancel₀ ε hrpos.ne'
    push_cast
    nlinarith
  have hm := weightedFrequencyMoment_le (smoothNumbers ((M : ℝ)^L) M)
    (fun n=>((n^k : ℕ) : ℤ)) (fun n=>(productWeight L M n : ℝ)) r
    (K := C*((M : ℝ)^L)^δ) (by positivity)
    (fun n _=>Nat.cast_nonneg _) (hw M hM)
  rw [← smoothMoment_even_eq_frequency] at hm
  have hEq : weightedFrequencyMoment (smoothNumbers ((M : ℝ)^L) M)
      (fun n=>((n^k : ℕ) : ℤ)) (fun n=>(productWeight L M n : ℝ)) r=
      productMoment k (2*r) L M := by
    unfold weightedFrequencyMoment productMoment
    rw [← productWeyl_eq_weightedFrequencySum k L M hM]
  rw [hEq,mul_pow,← Real.rpow_mul_natCast hp.le] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 he)
      (pow_nonneg hC.le _)) (smoothMoment_nonneg k (2*r) ((M : ℝ)^L) M))

#print axioms productWeyl_regroup_smooth
#print axioms productMoment_even_le_smooth
end Waring.EndgameCompletion
