import Waring.SeedCompletionPaddedSource

/-! # Uniform powers of the actual padded second moments -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionPaddedSource
open SeedCompletionWeylTransport SeedCompletionNaturalBox
open PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges CartesianProductSampling
open SeedCompletionSourceBounds SeedCompletionTerminalSparse SeedCompletionTerminalBox
open CoefficientPower SmoothMoments

def curveLoss {j : ℕ} (φ : Fin j→ℝ) : ℝ := max 0 (total φ-1/3)

def paddedNormalizer {j : ℕ} (k r : ℕ) (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) : ℝ :=
  ((D*P)+(D*P)^(2/3:ℝ)*(∏ i,P^(φ i)*R))*
    ((∏ i,boxHeights k (D*P) (fun i=>P^(φ i)) i)*(D*P)^r*(∏ i,P^(φ i)*R))

theorem coefficient_product_power {j : ℕ} {P : ℝ} (hP : 0<P)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (R : ℝ) :
    (∏ i,P^(φ i)*R)=P^(total φ)*R^j := by
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    power_parameters_product hP φ hφ]

theorem normalizer_nonneg {j : ℕ} (k r : ℕ) {D P R : ℝ} (φ : Fin j→ℝ)
    (hD : 0≤D) (hP : 0<P) (hR : 0≤R) : 0≤paddedNormalizer k r D φ P R := by
  unfold paddedNormalizer boxHeights
  positivity

theorem paddedNormalizer_power {k j : ℕ} (r : ℕ) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedNormalizer k r D φ)
      (1+parameterExponent k φ+(r:ℝ)+curveLoss φ) := by
  have hL : SourcePowerBound (fun P _=>D*P) 1 := by
    simpa only [zero_add,Real.rpow_one] using (constant D).mul (ambient_power 1)
  have hM : SourcePowerBound (fun P R=>∏ i,P^(φ i)*R) (total φ) := by
    have H := (ambient_power (total φ)).mul (smoothness_power.natPow j)
    norm_num only [zero_mul,add_zero] at H
    exact H.congr (fun P R hP _=>(coefficient_product_power (zero_lt_one.trans_le hP) φ hφ R).symm)
  have hH : SourcePowerBound
      (fun P _=>∏ i,boxHeights k (D*P) (fun i=>P^(φ i)) i)
      ((j:ℝ)-(k:ℝ)*total φ) := by
    have H := (constant (D^j)).mul (ambient_power ((j:ℝ)-(k:ℝ)*total φ))
    norm_num only [zero_add] at H
    exact H.congr (fun P R hP _=>
      (boxHeightProduct_power k (zero_lt_one.trans_le hP) D φ hshift).symm)
  have hLp := hL.rpow (show (0:ℝ)≤2/3 by norm_num)
    (fun P R hP _=>mul_nonneg (zero_le_one.trans hD) (zero_le_one.trans hP))
  have H := (hL.add (hLp.mul hM)).mul ((hH.mul (hL.natPow r)).mul hM)
  have hmax : max 1 (2/3+total φ)=1+curveLoss φ := by
    unfold curveLoss
    by_cases h : total φ≤1/3
    · rw [max_eq_left (by linarith),max_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by linarith),max_eq_right (by linarith)]
      ring
  norm_num only [one_mul] at H
  rw [hmax] at H
  convert H using 1
  unfold parameterExponent
  ring

theorem paddedMoment_one_eq_terminal {j : ℕ} (k r : ℕ)
    (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) :
    paddedMoment k r 1 D φ P R=paddedSecondMoment k
      (originalHeights k (D*P) (fun i=>P^(φ i)))
      (originalCoefficients P R (fun i=>P^(φ i)))
      (fun _ : Fin r=>rangeSet (D*P)) (rangeSet (D*P)) := by
  unfold paddedMoment
  rw [sourceMoment_one_eq_second]
  rfl

theorem originalCoefficients_card_le {j : ℕ} (P : ℝ) {R : ℝ}
    (M : Fin j→ℝ) (hR : 0≤R) (hM : ∀ i,0≤M i) (i : Fin j) :
    ((originalCoefficients P R M i).card : ℝ)≤M i*R := by
  calc
    _ ≤ ((smoothNumbers (M i*R) R).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (coefficientBlock_subset P R (M i))
    _ ≤ (⌊M i*R⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le (M i*R) R
    _ ≤ _ := Nat.floor_le (mul_nonneg (hM i) hR)

theorem padded_second_power {k j r : ℕ} (hk : k≤18) (hjk : j+r<k)
    (hj : 1≤j) (hJ : 2≤(k-(j+r))/2) (hjJ : j≤(k-(j+r))/2+1)
    {D : ℝ} (hD : 1≤D) (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i)
    (hφ1 : ∀ i,φ i≤1) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (paddedMoment k r 1 D φ)
      (1+parameterExponent k φ+(r:ℝ)+curveLoss φ) := by
  apply (paddedNormalizer_power r hD φ hφ hshift).of_epsilon_domination
  intro δ hδ
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := padded_second_moment_box hk hjk hj hJ hjJ
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
  rw [abs_of_nonneg (normalizer_nonneg k r φ hDp.le hPp (zero_le_one.trans hR))]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,paddedNormalizer]
  rw [Real.mul_rpow hDp.le hPp.le]
  ring

#print axioms paddedNormalizer_power
#print axioms padded_second_power
end Waring.SeedCompletionPaddedSource
