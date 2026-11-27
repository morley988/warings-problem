import Waring.AuxiliaryF6
import Waring.AdmissibleMinorArc

/-! The actual source-range pointwise amplitude and real/ENNReal F6 moments. -/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace Waring.AuxiliaryF6Cap
open AuxiliaryF6 AuxiliarySourceCount AuxiliarySmoothScales AuxiliaryFrozen AuxiliaryScales AuxiliaryTupleCount
open AuxiliaryCounting AuxiliaryL2Counting SmoothMoments

def amplitude8 : ℝ := 323249759/100000000
def innerLength8 : ℝ := 46178537/100000000
def innerCutoff8 (P : ℝ) : ℝ := 64*P^innerLength8

theorem innerLength8_pos : 0 < innerLength8 := by norm_num [innerLength8]

theorem innerLength8_eq : innerLength8=1-∑ i ∈ Finset.range 6, phi8 i := by
  norm_num [innerLength8,phi8,phi8Q,Finset.sum_range_succ]

theorem amplitude8_eq :
    (∑ i ∈ Finset.range 6, shiftExponent8 i)+(∑ i ∈ Finset.range 6, phi8 i)+1=amplitude8 := by
  rw [← Finset.sum_add_distrib,diagonal_exponent8]
  norm_num [amplitude8]

theorem fullH_card_bound {P : ℝ} (hP : 0 < P) :
    ((fullH P).card : ℝ) ≤ (64 : ℝ)^6*P^(∑ i ∈ Finset.range 6, shiftExponent8 i) := by
  rw [fullH,coordinateBox_card,Nat.cast_prod]
  calc
    _ ≤ ∏ i ∈ Finset.range 6, (64*P^(shiftExponent8 i)) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i hi => Nat.floor_le (by positivity))
    _ = _ := by rw [Finset.prod_mul_distrib,← Real.rpow_sum_of_pos hP]; simp

theorem fullM_card_bound {P R : ℝ} (hP : 0 < P) (hR : 0 ≤ R) :
    ((fullM P R).card : ℝ) ≤ P^(∑ i ∈ Finset.range 6, phi8 i)*R^6 := by
  rw [fullM,coordinateBox_card,Nat.cast_prod]
  calc
    _ ≤ ∏ i ∈ Finset.range 6, (P^(phi8 i)*R) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i hi => Nat.floor_le (by positivity))
    _ = _ := by rw [Finset.prod_mul_distrib,← Real.rpow_sum_of_pos hP]; simp

/-- Literal finite-sum amplitude with all fixed source factors and R^6. -/
theorem actualF6_trivial {P R : ℝ} (hP : 0 < P) (hR : 0 ≤ R) (α : ℝ) :
    ‖actualF6 P R α‖ ≤ (64 : ℝ)^7*P^amplitude8*R^6 := by
  have hn : ‖actualF6 P R α‖ ≤
      ((fullH P).card : ℝ)*((sourceM P R).card : ℝ)*((zRange P).card : ℝ) := by
    rw [actualF6_fourier]
    calc
      _ ≤ ∑ x ∈ AuxiliaryL2Counting.indexSet (fullH P) (sourceM P R) (zRange P),
          ‖fourier (frequency 430080 16 x) (α : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ = _ := by
        have hchar (n : ℤ) : ‖fourier n (α : AddCircle (1 : ℝ))‖=1 := Circle.norm_coe _
        simp_rw [hchar]
        simp only [Finset.sum_const,nsmul_eq_mul,mul_one,indexSet,Finset.card_product,Nat.cast_mul]
        ring
  have hM : ((sourceM P R).card : ℝ) ≤ P^(∑ i ∈ Finset.range 6, phi8 i)*R^6 :=
    le_trans (by exact_mod_cast Finset.card_le_card (sourceM_subset P R)) (fullM_card_bound hP hR)
  have hZ : ((zRange P).card : ℝ) ≤ 64*P := by
    have hc : (zRange P).card=⌊64*P⌋₊ := by simp [zRange,Int.card_Icc]
    rw [hc]
    exact Nat.floor_le (by positivity)
  have hpowers : P^(∑ i ∈ Finset.range 6, shiftExponent8 i)*
      P^(∑ i ∈ Finset.range 6, phi8 i)*P=P^amplitude8 := by
    nth_rw 3 [← Real.rpow_one P]
    rw [← Real.rpow_add hP,← Real.rpow_add hP,amplitude8_eq]
  calc
    _ ≤ ((fullH P).card : ℝ)*((sourceM P R).card : ℝ)*((zRange P).card : ℝ) := hn
    _ ≤ ((64 : ℝ)^6*P^(∑ i ∈ Finset.range 6, shiftExponent8 i))*
        (P^(∑ i ∈ Finset.range 6, phi8 i)*R^6)*(64*P) := by
      exact mul_le_mul (mul_le_mul (fullH_card_bound hP) hM (by positivity) (by positivity))
        hZ (by positivity) (by positivity)
    _ = (64 : ℝ)^7*(P^(∑ i ∈ Finset.range 6, shiftExponent8 i)*
        P^(∑ i ∈ Finset.range 6, phi8 i)*P)*R^6 := by ring
    _ = _ := by rw [hpowers]

/-- The conventional epsilon form of the actual trivial pointwise cap. -/
theorem actualF6_pointwise {P R η ε : ℝ} (hP : 1 ≤ P) (hR : 0 ≤ R)
    (hRP : R ≤ P^η) (hηε : 6*η ≤ ε) (α : ℝ) :
    ‖actualF6 P R α‖ ≤ (64 : ℝ)^7*P^(amplitude8+ε) := by
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hRpow : R^6 ≤ P^ε := by
    calc
      _ ≤ (P^η)^6 := pow_le_pow_left₀ hR hRP 6
      _ = P^(η*6) := (Real.rpow_mul_natCast hPpos.le η 6).symm
      _ ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  calc
    _ ≤ (64 : ℝ)^7*P^amplitude8*R^6 := actualF6_trivial hPpos hR α
    _ ≤ (64 : ℝ)^7*P^amplitude8*P^ε := mul_le_mul_of_nonneg_left hRpow (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hPpos]

theorem continuous_actualF6 (P R : ℝ) : Continuous (actualF6 P R) := by
  have heq : actualF6 P R = fun (α : ℝ) => ∑ x ∈ indexSet (fullH P) (sourceM P R) (zRange P),
      fourier (frequency 430080 16 x) (α : AddCircle (1 : ℝ)) := funext (actualF6_fourier P R)
  rw [heq]
  exact continuous_finset_sum _ (fun x hx =>
    (fourier (frequency 430080 16 x)).continuous.comp (AddCircle.continuous_mk' 1))

theorem actualF6_full_lintegral (P R : ℝ) :
    (∫⁻ α, (ENNReal.ofReal ‖actualF6 P R α‖)^2 ∂volume.restrict (Set.Ioc 0 1)) =
      ENNReal.ofReal (∫ α in (0 : ℝ)..1, ‖actualF6 P R α‖^2) := by
  have hi : IntervalIntegrable (fun α : ℝ => ‖actualF6 P R α‖^2) volume 0 1 :=
    ((continuous_actualF6 P R).norm.pow 2).intervalIntegrable (0 : ℝ) 1
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal hi.1 (Filter.Eventually.of_forall (fun α => sq_nonneg _))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

#print axioms actualF6_trivial
#print axioms actualF6_pointwise
#print axioms actualF6_full_lintegral
end Waring.AuxiliaryF6Cap
