import Waring.AuxiliaryL2
import Waring.AuxiliarySourceCount
import Waring.AuxiliaryFrequencyBounds
import Waring.SourcePhaseConstants

/-!
# The actual frozen degree-eight F6 second moment

This module proves the L2 auxiliary estimate for the actual modified centered
power polynomial, with its source normalization and smooth coefficient ranges.
The fixed source factors 64, both divisor losses, the coefficient zero count,
all floor cutoffs and the final P^epsilon allocation are explicit and proved.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryF6
open AuxiliaryL2Grouping AuxiliaryL2Counting AuxiliaryL2 AuxiliaryTupleCount
open AuxiliaryCounting AuxiliaryScales AuxiliaryFrozen AuxiliarySmoothScales AuxiliarySourceCount
open AuxiliaryFrequencyBounds PolynomialSumReduction SmoothMoments

def fullH (P : ℝ) := coordinateBox (sourceShiftScale P) 6
def fullM (P R : ℝ) := coordinateBox (smoothCoefficientScale P R) 6
def zRange (P : ℝ) : Finset ℤ := Finset.Icc 1 (⌊64*P⌋₊ : ℤ)

private theorem H_pos {P : ℝ} {h : Fin 6 → ℕ} (hh : h ∈ fullH P) (i : Fin 6) : 0 < h i := by
  have hi := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hh i)).1
  omega

private theorem M_pos {P R : ℝ} {m : Fin 6 → ℕ} (hm : m ∈ fullM P R) (i : Fin 6) : 0 < m i := by
  have hi := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm i)).1
  omega

private theorem H_bound {P : ℝ} (hP : 1 ≤ P) {h : Fin 6 → ℕ} (hh : h ∈ fullH P)
    (i : Fin 6) : (h i : ℝ) ≤ 64*P := by
  have hi := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hh i)).2
  exact le_trans (by exact_mod_cast hi) (sourceShiftScale_real_le hP i.isLt)

private theorem M_bound {P R η : ℝ} (hP : 1 ≤ P) (hηcap : η ≤ 1/100000000)
    (hRP : R ≤ P^η) {m : Fin 6 → ℕ} (hm : m ∈ fullM P R) (i : Fin 6) : (m i : ℝ) ≤ 64*P := by
  have hi := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hm i)).2
  have hsmall : (m i : ℝ) ≤ P := le_trans (by exact_mod_cast hi)
    (smoothCoefficientScale_real_le hP hηcap hRP i.isLt)
  linarith

private theorem zRange_bound {P : ℝ} (hP : 0 ≤ P) {z : ℤ} (hz : z ∈ zRange P) :
    |(z : ℝ)| ≤ 64*P := by
  rcases Finset.mem_Icc.mp hz with ⟨hz1,hzP⟩
  have hz0 : (0 : ℝ) ≤ z := by exact_mod_cast (show (0 : ℤ) ≤ z by omega)
  rw [abs_of_nonneg hz0]
  exact le_trans (by exact_mod_cast hzP) (Nat.floor_le (by positivity))

private theorem zRange_card_le {P : ℝ} (hP : 0 ≤ P) : (zRange P).card ≤ ⌊64*P⌋₊ := by
  simp [zRange,Int.card_Icc]

/-- The actual integer-frequency second moment over the full source boxes. -/
theorem frozen_full_secondMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R : ℝ, 1 ≤ R → R ≤ P^(sourceEta (ε/2)) →
      auxiliaryMoment 430080 16 (fullH P) (fullM P R) (zRange P) ≤
        C*P^((323249759/100000000 : ℝ)+ε) := by
  let δ : ℝ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,hmoment⟩ := auxiliaryMoment_le_coefficientCount 6
    (show (0 : ℝ) ≤ 25 by norm_num) (show (0 : ℝ) ≤ 20 by norm_num) hδ
  obtain ⟨D,hD,P₀,hP₀,hcount⟩ := frozen_source_zeroCount hδ
  refine ⟨K*(64 : ℝ)^(1+δ)*D,by positivity,max P₀ 3870720,
    hP₀.trans (le_max_left _ _),?_⟩
  intro P hP R hR hRP
  have hP0 : P₀ ≤ P := (le_max_left _ _).trans hP
  have hPbig : 3870720 ≤ P := (le_max_right _ _).trans hP
  have hP1 : 1 ≤ P := hP₀.trans hP0
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  have hQ1 : 1 ≤ 64*P := by linarith
  have hQbig : 3870720 ≤ 64*P := by linarith
  have hηcap := sourceEta_le δ
  have hshift : ∀ h ∈ fullH P, shiftProduct h ≠ 0 := by
    intro h hh
    apply ne_of_gt
    exact Finset.prod_pos (fun i hi => by exact_mod_cast H_pos hh i)
  have hfreq : ∀ x ∈ indexSet (fullH P) (fullM P R) (zRange P),
      frequency 430080 16 x ≠ 0 ∧ ((frequency 430080 16 x).natAbs : ℝ) ≤ (64*P)^(25 : ℝ) := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    refine ⟨(frequency_pos x.1 x.2.1 x.2.2 (H_pos hh) (M_pos hm)).ne',?_⟩
    norm_num only [Real.rpow_ofNat]
    exact frequency_natAbs_le hQbig x.1 x.2.1 x.2.2 (H_pos hh) (M_pos hm)
      (H_bound hP1 hh) (M_bound hP1 hηcap hRP hm) (zRange_bound hPpos.le hz)
  have hcoef : ∀ h ∈ fullH P, ∀ m ∈ fullM P R, ∀ n ∈ fullM P R,
      ((coefficientValue 16 h n-coefficientValue 16 h m).natAbs : ℝ) ≤ (64*P)^(20 : ℝ) := by
    intro h hh m hm n hn
    norm_num only [Real.rpow_ofNat]
    exact coefficient_difference_natAbs_le (by linarith) h n m
      (H_bound hP1 hh) (M_bound hP1 hηcap hRP hn) (M_bound hP1 hηcap hRP hm)
  have hMcard : ((fullM P R).card : ℝ) ≤ 64*P :=
    (smooth_coefficient_tuple_card_le hP1 hηcap hRP).trans (by linarith)
  have hZcard : ((zRange P).card : ℝ) ≤ 3*(64*P) := by
    have hc : ((zRange P).card : ℝ) ≤ (⌊64*P⌋₊ : ℝ) := by exact_mod_cast zRange_card_le hPpos.le
    have hf := Nat.floor_le (show 0 ≤ 64*P by positivity)
    linarith
  have hl2 := hmoment (64*P) hQ1 430080 (by norm_num) 16 (fullH P) (fullM P R) (zRange P)
    hshift hfreq hcoef hMcard hZcard
  have hNc : (coefficientCollisionCount 16 (fullH P) (fullM P R) : ℝ) ≤
      D*P^((223249759/100000000 : ℝ)+δ) := by
    have hc : (coefficientCollisionCount 16 (fullH P) (fullM P R) : ℝ) ≤
        (zeroCount 16 (prefixFamily (sourceShiftScale P) (smoothCoefficientScale P R) 6) : ℝ) := by
      exact_mod_cast coefficientCollisionCount_le_zeroCount 16 6 (sourceShiftScale P) (smoothCoefficientScale P R)
    exact hc.trans (hcount P hP0 R hR hRP)
  calc
    _ ≤ K*(64*P)^(1+δ)*(coefficientCollisionCount 16 (fullH P) (fullM P R) : ℝ) := hl2
    _ ≤ K*(64*P)^(1+δ)*(D*P^((223249759/100000000 : ℝ)+δ)) :=
      mul_le_mul_of_nonneg_left hNc (by positivity)
    _ = (K*(64 : ℝ)^(1+δ)*D)*P^((323249759/100000000 : ℝ)+ε) := by
      rw [Real.mul_rpow (by norm_num) hPpos.le]
      have hexp : (1+δ)+((223249759/100000000 : ℝ)+δ)=(323249759/100000000 : ℝ)+ε := by
        dsimp [δ]
        ring
      have hpowers : P^(1+δ)*P^((223249759/100000000 : ℝ)+δ)=
          P^((323249759/100000000 : ℝ)+ε) := by
        rw [← Real.rpow_add hPpos,hexp]
      calc
        _ = (K*(64 : ℝ)^(1+δ)*D)*(P^(1+δ)*P^((223249759/100000000 : ℝ)+δ)) := by ring
        _ = _ := by rw [hpowers]

/-- The actual source coefficient interval, including smoothness and the
strict lower cutoff M_i<m_i. -/
def sourceCoefficientSet (P R : ℝ) (i : Fin 6) : Finset ℕ := by
  classical
  exact (smoothNumbers P R).filter (fun m => P^(phi8 i.val)<(m : ℝ) ∧ (m : ℝ)≤P^(phi8 i.val)*R)

def sourceM (P R : ℝ) : Finset (Fin 6 → ℕ) := Fintype.piFinset (sourceCoefficientSet P R)

def actualF6 (P R α : ℝ) : ℂ :=
  polynomialFamily 8 (fullH P ×ˢ sourceM P R)
    (fun hm i => (hm.1 i : ℝ)) (fun hm i => (hm.2 i : ℝ)) α 1 (⌊64*P⌋₊ : ℤ)

theorem sourceM_subset (P R : ℝ) : sourceM P R ⊆ fullM P R := by
  intro m hm
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := Finset.mem_filter.mp (Fintype.mem_piFinset.mp hm i)
  have hpos := (mem_smoothNumbers.mp hi.1).1.1
  exact Finset.mem_Icc.mpr ⟨hpos,(Nat.le_floor_iff' (by omega)).mpr hi.2.2⟩

theorem actualF6_fourier (P R α : ℝ) :
    actualF6 P R α = ∑ x ∈ indexSet (fullH P) (sourceM P R) (zRange P),
      fourier (frequency 430080 16 x) (α : AddCircle (1 : ℝ)) := by
  apply SourcePhaseConstants.k8_j6_family_fourier
  intro m hm i
  exact (M_pos (sourceM_subset P R hm) i).ne'

theorem auxiliaryMoment_mono_M {r : ℕ} (C : ℤ) (k : ℕ) (H : Finset (Fin r → ℕ))
    {M N : Finset (Fin r → ℕ)} (hMN : M ⊆ N) (Z : Finset ℤ) :
    auxiliaryMoment C k H M Z ≤ auxiliaryMoment C k H N Z := by
  have hA : indexSet H M Z ⊆ indexSet H N Z :=
    Finset.product_subset_product (Finset.Subset.refl _) (Finset.product_subset_product hMN (Finset.Subset.refl _))
  exact frequencyEvenMoment_mono hA (frequency C k) 1

/-- Unconditional actual F6 L2 bound in the canonical frozen policy, with the
full source cutoffs and a single positive smoothness exponent for every R.
This theorem has no efficient-differencing source estimate among its premises. -/
theorem actualF6_secondMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      (∫ α in (0 : ℝ)..1, ‖actualF6 P R α‖^2) ≤
        C*P^((323249759/100000000 : ℝ)+ε) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := frozen_full_secondMoment hε
  refine ⟨sourceEta (ε/2),sourceEta_pos (by positivity),C,hC,P₀,hP₀,?_⟩
  intro P hP R hR hRP
  simp_rw [actualF6_fourier]
  exact (auxiliaryMoment_mono_M 430080 16 (fullH P) (sourceM_subset P R) (zRange P)).trans
    (hbound P hP R hR hRP)

#print axioms frozen_full_secondMoment
#print axioms actualF6_fourier
#print axioms actualF6_secondMoment
end Waring.AuxiliaryF6
