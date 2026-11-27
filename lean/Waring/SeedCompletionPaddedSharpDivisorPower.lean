import Waring.SeedCompletionSharpDivisorReal
import Waring.SeedCompletionSharpPowerScales

/-! # Sharp actual padded source powers under the elementary divisor prefix criterion -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionPaddedSource
open SeedCompletionWeylTransport SeedCompletionNaturalBox
open PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges CartesianProductSampling
open SeedCompletionSourceBounds SeedCompletionTerminalSparse
open SeedCompletionTerminalDivisorReal SeedCompletionDivisorPowerScales
open SeedCompletionSharpDivisorReal SeedCompletionSharpPowerScales
open PolicyCompletionSharpResidualSource
open CoefficientPower SmoothMoments

theorem padded_second_sharp_divisor_power {k j r : ℕ} (hk : k≤18) (hjk : j+r+2≤k)
    (hj : 1≤j) (hgood : SharpResidual k (j+r)) {D : ℝ} (hD : 1≤D) (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i)
    (hφ1 : ∀ i,φ i≤1) (hshift : ∀ i,0≤shiftExponents k φ i)
    (hprefix : PrefixCondition k φ) :
    SourcePowerBound (paddedMoment k r 1 D φ)
      (1+parameterExponent k φ+(r:ℝ)) := by
  apply (sharpDivisorNormalizer_power (by omega) r hD φ hφ hshift).of_epsilon_domination
  intro δ hδ
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := sharp_padded_second_moment_divisor_real_box hk hjk hj hgood hδ
  refine ⟨1,by norm_num,?_⟩
  intro η hη hηle
  refine ⟨C*D^δ,mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le hD) _),
    P₀,by linarith,?_⟩
  intro P hPP
  have hP : 1≤P := by linarith
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hL : 1≤D*P := one_le_mul_of_one_le_of_one_le hD hP
  have hPL : P≤D*P := le_mul_of_one_le_left hPp.le hD
  have hR : 1≤P^η := Real.one_le_rpow hP hη.le
  have hRP : P^η≤P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hηle
  let M : ℕ→ℝ := fun i=>P^(phiExtend φ i)
  let Hcap : ℕ→ℝ := fun i=>D*P^(1-(k:ℝ)*phiExtend φ i)
  have hMval (i : Fin j) : M i.val=P^(φ i) := by simp only [M,phiExtend_fin]
  have hHval (i : Fin j) : Hcap i.val=boxHeights k (D*P) (fun i=>P^(φ i)) i := by
    rw [boxHeights_power k hPp D φ]
    simp only [Hcap,phiExtend_fin,shiftExponents]
  have hM (i : ℕ) (hi : i<j) : 1≤M i ∧ M i≤D*P := by
    rw [show M i=P^(φ ⟨i,hi⟩) from hMval ⟨i,hi⟩]
    refine ⟨Real.one_le_rpow hP (hφ _),?_⟩
    exact (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hP (hφ1 ⟨i,hi⟩) : P^(φ ⟨i,hi⟩)≤P).trans hPL
  have hHcap (i : ℕ) (hi : i<j) : 1≤Hcap i ∧ Hcap i≤D*P := by
    rw [show Hcap i=D*P^(shiftExponents k φ ⟨i,hi⟩) by simp [Hcap,phiExtend,hi,shiftExponents]]
    refine ⟨one_le_mul_of_one_le_of_one_le hD (Real.one_le_rpow hP (hshift _)),?_⟩
    apply mul_le_mul_of_nonneg_left _ hDp.le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
      (show shiftExponents k φ ⟨i,hi⟩≤1 by
        unfold shiftExponents
        have hkR : (0:ℝ)≤k := Nat.cast_nonneg _
        nlinarith [hφ ⟨i,hi⟩])
  have hb := hbound (D*P) (hPP.trans hPL) (P^η) hR (hRP.trans hPL) Hcap M
    hHcap hM (power_prefix_condition hD hP φ hφ hprefix)
    (originalHeights k (D*P) (fun i=>P^(φ i)))
    (originalCoefficients P (P^η) (fun i=>P^(φ i)))
    (fun _ : Fin r=>rangeSet (D*P))
    (by
      intro i h hh
      have hh := Finset.mem_Icc.mp hh
      refine ⟨hh.1,?_⟩
      rw [hHval]
      have hc : 0≤boxHeights k (D*P) (fun i=>P^(φ i)) i := by
        rw [← hHval]; exact zero_le_one.trans (hHcap i.val i.isLt).1
      exact (by exact_mod_cast hh.2 : (h:ℝ)≤⌊boxHeights k (D*P) (fun i=>P^(φ i)) i⌋₊).trans
        (Nat.floor_le hc))
    (by
      intro i m hm
      refine ⟨(mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1,?_⟩
      rw [hMval]
      exact (Finset.mem_filter.mp hm).2.2)
    (by
      intro i h hh
      have hh := Finset.mem_Icc.mp hh
      refine ⟨hh.1,?_⟩
      exact (by exact_mod_cast hh.2 : (h:ℝ)≤⌊D*P⌋₊).trans (Nat.floor_le (zero_le_one.trans hL)))
    (rangeSet (D*P)) (by
      intro z hz
      have hz := Finset.mem_Icc.mp hz
      refine ⟨hz.1,?_⟩
      exact (by exact_mod_cast hz.2 : (z:ℝ)≤⌊D*P⌋₊).trans (Nat.floor_le (zero_le_one.trans hL)))
    (rangeSet_card_le (zero_le_one.trans hL))
  simp only [hMval,hHval] at hb
  have hgcard : ((Fintype.piFinset (fun _ : Fin r=>rangeSet (D*P))).card:ℝ)≤(D*P)^r := by
    rw [Fintype.card_piFinset,Nat.cast_prod]
    calc
      _ ≤ ∏ _ : Fin r,D*P := Finset.prod_le_prod (fun _ _=>Nat.cast_nonneg _)
        (fun _ _=>rangeSet_card_le (zero_le_one.trans hL))
      _ = _ := by simp
  have hHpos (i : Fin j) : 0≤boxHeights k (D*P) (fun i=>P^(φ i)) i := by
    rw [← hHval]; exact zero_le_one.trans (hHcap i.val i.isLt).1
  have hprodH : 0≤∏ i,boxHeights k (D*P) (fun i=>P^(φ i)) i :=
    Finset.prod_nonneg (fun i _=>hHpos i)
  have hprodM : 0≤∏ i,P^(φ i)*P^η := Finset.prod_nonneg (fun _ _=>by positivity)
  have hswell := swellFactor_nonneg j (zero_le_one.trans hR)
  rw [abs_of_nonneg (paddedMoment_nonneg ..),paddedMoment_one_eq_terminal]
  apply hb.trans
  calc
    _ ≤ C*(D*P)^δ*swellFactor j (P^η)*
        ((D*P)+(∏ i,P^(φ i)*P^η))*
        (∏ i,boxHeights k (D*P) (fun i=>P^(φ i)) i)*(∏ i,P^(φ i)*P^η)*(D*P)^r :=
      mul_le_mul_of_nonneg_left hgcard (by positivity)
    _ = _ := by
      rw [abs_of_nonneg (sharpDivisorNormalizer_nonneg k r φ hDp.le hPp (zero_le_one.trans hR))]
      unfold sharpDivisorNormalizer sharpNormalizer
      rw [Real.mul_rpow hDp.le hPp.le]
      ring

#print axioms padded_second_sharp_divisor_power
end Waring.SeedCompletionPaddedSource
