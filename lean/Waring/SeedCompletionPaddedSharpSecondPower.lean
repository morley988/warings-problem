import Waring.SeedCompletionSharpPowerScales
import Waring.PolicyCompletionSharpResidualBox

/-! # Sharp actual padded second-moment powers from sparse condition (i) -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionPaddedSource
open SeedCompletionWeylTransport SeedCompletionNaturalBox
open PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges CartesianProductSampling
open SeedCompletionSourceBounds SeedCompletionTerminalSparse SeedCompletionTerminalBox
open PolicyCompletionSharpResidualBox PolicyCompletionSharpResidualSource
open SeedCompletionSharpPowerScales
open CoefficientPower SmoothMoments

theorem padded_second_sharp_power {k j r : ℕ} (hk : k≤18) (hjk : j+r<k)
    (hj : 1≤j) (hgood : SharpResidual k (j+r)) (hJ : 2≤(k-(j+r))/2) (hjJ : j≤(k-(j+r))/2+1)
    {D : ℝ} (hD : 1≤D) (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i)
    (hφ1 : ∀ i,φ i≤1) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedMoment k r 1 D φ)
      (1+parameterExponent k φ+(r:ℝ)) := by
  apply (sharpNormalizer_power (by omega) r hD φ hφ hshift).of_epsilon_domination
  intro δ hδ
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := sharp_padded_second_moment_box hk hjk hj hgood hJ hjJ
    (B:=2) (by norm_num) hδ
  refine ⟨1,by norm_num,?_⟩
  intro η hη hηle
  refine ⟨C*D^δ,mul_pos hC (Real.rpow_pos_of_pos (zero_lt_one.trans_le hD) _),
    P₀,hP₀,?_⟩
  intro P hPP
  have hP : 1≤P := hP₀.trans hPP
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hL : 1≤D*P := one_le_mul_of_one_le_of_one_le hD hP
  have hPL : P≤D*P := le_mul_of_one_le_left hPp.le hD
  have hL2 : D*P≤(D*P)^2 := le_self_pow₀ hL (by norm_num)
  have hM (i : Fin j) : 1≤P^(φ i) := Real.one_le_rpow hP (hφ i)
  have hMP (i : Fin j) : P^(φ i)≤P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP (hφ1 i)
  have hR : 1≤P^η := Real.one_le_rpow hP hη.le
  have hRP : P^η≤P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hηle
  have hHpos (i : Fin j) : 0<boxHeights k (D*P) (fun i=>P^(φ i)) i :=
    boxHeights_pos k (mul_pos hDp hPp) (fun i=>Real.rpow_pos_of_pos hPp _) i
  have hHP (i : Fin j) : boxHeights k (D*P) (fun i=>P^(φ i)) i≤D*P :=
    div_le_self (zero_le_one.trans hL) (one_le_pow₀ (hM i))
  have hcap (i : Fin j) : P^(φ i)*P^η≤(D*P)^(2:ℝ) := by
    rw [Real.rpow_two]
    exact (mul_le_mul (hMP i) hRP (by positivity) hPp.le).trans (by nlinarith)
  have hb := hbound (D*P) (hPP.trans hPL)
    (originalHeights k (D*P) (fun i=>P^(φ i)))
    (originalCoefficients P (P^η) (fun i=>P^(φ i)))
    (fun _ : Fin r=>rangeSet (D*P))
    (boxHeights k (D*P) (fun i=>P^(φ i))) (fun i=>P^(φ i)*P^η)
    (fun _ : Fin r=>D*P) hHpos
    (fun i=>rangeSet_card_le (hHpos i).le) (fun _=>mul_pos hDp hPp)
    (fun _=>rangeSet_card_le (zero_le_one.trans hL))
    (by
      intro i h hh
      have hh := Finset.mem_Icc.mp hh
      refine ⟨hh.1,?_⟩
      have hh' : (h:ℝ)≤boxHeights k (D*P) (fun i=>P^(φ i)) i :=
        (by exact_mod_cast hh.2 : (h:ℝ)≤⌊boxHeights k (D*P) (fun i=>P^(φ i)) i⌋₊).trans
          (Nat.floor_le (hHpos i).le)
      simpa only [Real.rpow_two] using hh'.trans ((hHP i).trans hL2))
    (by
      intro i h hh
      have hh := Finset.mem_Icc.mp hh
      refine ⟨hh.1,?_⟩
      have hh' : (h:ℝ)≤D*P :=
        (by exact_mod_cast hh.2 : (h:ℝ)≤⌊D*P⌋₊).trans (Nat.floor_le (zero_le_one.trans hL))
      simpa only [Real.rpow_two] using hh'.trans hL2)
    (by
      intro i m hm
      exact ⟨(mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1,
        (Finset.mem_filter.mp hm).2.2⟩)
    (fun i=>one_le_mul_of_one_le_of_one_le (hM i) hR) hcap
    (fun i=>originalCoefficients_card_le P _ (zero_le_one.trans hR)
      (fun i=>(Real.rpow_pos_of_pos hPp (φ i)).le) i)
    (rangeSet (D*P)) (by
      intro z hz
      have hz := Finset.mem_Icc.mp hz
      refine ⟨hz.1,?_⟩
      exact (by exact_mod_cast hz.2 : (z:ℝ)≤⌊D*P⌋₊).trans (Nat.floor_le (zero_le_one.trans hL)))
    (rangeSet_card_le (zero_le_one.trans hL))
  rw [abs_of_nonneg (paddedMoment_nonneg ..),paddedMoment_one_eq_terminal]
  apply hb.trans_eq
  rw [abs_of_nonneg (sharpNormalizer_nonneg k r φ hDp.le hPp (zero_le_one.trans hR))]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,sharpNormalizer]
  rw [Real.mul_rpow hDp.le hPp.le]
  ring

#print axioms padded_second_sharp_power
end Waring.SeedCompletionPaddedSource
