import Waring.PolicyCompletionSourceCartesian
import Waring.PolicyCompletionMinorGeometry
import Waring.AuxiliaryF6Cap

/-! # The actual frozen auxiliary moment is the literal dilated source moment -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace Waring.PolicyCompletionAuxiliarySource
open Certificate SmoothMoments PolynomialSumReduction IntegerDifferencePolynomial
open PolicyCompletionMajorFamily PolicyCompletionSourceMajor PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges PolicyCompletionSourceCartesian
open AuxiliaryF6 AuxiliaryF6Cap AuxiliaryFrozen AuxiliarySourceCount AuxiliaryTupleCount

theorem sourceFamily_eq_natural_family {j : ℕ} (k : ℕ) (S T : Finset (Fin j→ℕ))
    (L α : ℝ) (hT : ∀m∈T,∀i,m i≠0) :
    sourceFamily k S T L α=polynomialFamily k (S×ˢT)
      (fun hm i=>(hm.1 i:ℝ)) (fun hm i=>(hm.2 i:ℝ)) α 1 (⌊L⌋₊:ℤ) := by
  unfold sourceFamily polynomialFamily UnseparatedDifferencing.familySum
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro m hm
  rw [integerPolynomialWeyl_eq_source_sum k _ ?_,naturalParameters_real,
    sum_int_Icc_nat_complex]
  · rfl
  · simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro i
    exact_mod_cast hT m hm i

theorem frozen_phi_real (i : Fin 6) : phiReal policies8[0]! i=phi8 i.val := by
  change (policies8[0]!.phi[i.val]!:ℝ)=(phi8Q[i.val]!:ℝ)
  rw [phi8Q_eq_frozen]

theorem frozen_amplitude : amplitude 8 (phiReal policies8[0]!)=(323249759/100000000:ℝ) := by
  have hh : (phiReal policies8[0]!:Fin 6→ℝ)=fun i=>phi8 i.val := funext frozen_phi_real
  rw [hh]
  change 1+(6:ℝ)-8*(∑i : Fin 6,phi8 i.val)+(∑i : Fin 6,phi8 i.val)=(323249759/100000000:ℝ)
  norm_num [Fin.sum_univ_succ,phi8,phi8Q]

theorem source_box_eq_actualF6 {P : ℝ} (hP : 0<P) (R α : ℝ) :
    boxSourceFamily 8 (64*P) P R (fun i=>P^(phiReal policies8[0]! i)) α=actualF6 P R α := by
  have hb : boxHeightBounds 8 (64*P) (fun i=>P^(phiReal policies8[0]! i))=
      (fun i : Fin 6=>sourceShiftScale P i.val) := by
    funext i
    unfold boxHeightBounds
    rw [boxHeights_power 8 hP 64 (phiReal policies8[0]!) i]
    simp only [sourceShiftScale,shiftExponents,shiftExponent8,frozen_phi_real,Nat.cast_ofNat]
  have hc : (fun i : Fin 6=>CoefficientPower.coefficientBlock P R (P^(phiReal policies8[0]! i)))=
      sourceCoefficientSet P R := by
    funext i
    rw [frozen_phi_real]
    rfl
  unfold boxSourceFamily boxCoefficientTuples
  rw [hb]
  dsimp only
  change sourceFamily 8 (CartesianProductSampling.positiveBox (fun i : Fin 6=>sourceShiftScale P i.val))
    (Fintype.piFinset (fun i : Fin 6=>CoefficientPower.coefficientBlock P R (P^(phiReal policies8[0]! i))))
    (64*P) α=actualF6 P R α
  rw [hc]
  change sourceFamily 8 (fullH P) (sourceM P R) (64*P) α=actualF6 P R α
  apply sourceFamily_eq_natural_family
  intro m hm i
  have hp := (mem_smoothNumbers.mp (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hm i)).1).1.1
  omega

theorem frozen_source_second_lintegral {ε : ℝ} (hε : 0<ε) :
    ∃η : ℝ,0<η ∧ ∃C : ℝ,0<C ∧ ∃P₀ : ℝ,1≤P₀ ∧ ∀P : ℝ,P₀≤P→
      ∀R : ℝ,1≤R→R≤P^η→
      (∫⁻(α : ℝ),(ENNReal.ofReal ‖boxSourceFamily 8 (64*P) P R
        (fun i=>P^(phiReal policies8[0]! i)) α‖)^2 ∂volume.restrict (Set.Ioc 0 1))≤
      ENNReal.ofReal (C*P^(amplitude 8 (phiReal policies8[0]!)+ε)) := by
  obtain ⟨η,hη,C,hC,P₀,hP₀,hb⟩:=actualF6_secondMoment hε
  refine ⟨η,hη,C,hC,P₀,hP₀,?_⟩
  intro P hPP R hR hRP
  simp_rw [source_box_eq_actualF6 (zero_lt_one.trans_le (hP₀.trans hPP))]
  rw [actualF6_full_lintegral,frozen_amplitude]
  exact ENNReal.ofReal_le_ofReal (hb P hPP R hR hRP)

#print axioms source_box_eq_actualF6
#print axioms frozen_source_second_lintegral
end Waring.PolicyCompletionAuxiliarySource
