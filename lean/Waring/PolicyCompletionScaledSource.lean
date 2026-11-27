import Waring.PolicyCompletionScaledSample

/-! The basic and shallow sampled bounds for any fixed positive dilation
of both integer cutoffs. Auxiliary exponent slack is fully absorbed in the
requested epsilon, so the original literal cap hypotheses are unchanged. -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledSource
open NormalizedCoefficient RationalHeight CartesianFloorScales
open PolicyCompletionBasicRanges PolicyCompletionScaledSample

theorem normalized_basic_scaled_cutoffs {d c : ℕ} (hd : 6≤d) (hc : 0<c)
    {CH CJ h j phi b ε : ℝ} (hCH : 1≤CH) (hCJ : 1≤CJ)
    (hh : 0<h) (hj : 0≤j) (hphi : 0<phi) (hb : 0<b) (hε : 0<ε)
    (hcapPhi : b≤phi)
    (hcapCubic : 3*h+b≤j)
    (hcapPower : 2*(d : ℝ)*b≤3*h+j+(d : ℝ)*phi)
    (hcapBinomial : 6*b+((d-1 : ℕ) : ℝ)*phi≤3*h+j) :
    ∃η C P₀ : ℝ,0<η ∧ 0<C ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀(α : ℝ) (σ : ℕ→ℝ),
      P^((d : ℝ)*b/2)≤height (P^(3*h+j+(d : ℝ)*phi)) α→
      normalizedSampledCoefficient A d 1 P phi ⌊CH*P^h⌋₊ ⌈CJ*P^j⌉₊ ((c : ℝ)*α) σ≤
        C*P^(ε-b) := by
  let δ := min (b/4) (ε/16)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hδb : δ≤b/4 := min_le_left _ _
  have hδε : δ≤ε/16 := min_le_right _ _
  have hb' : 0<b-2*δ := by linarith
  have hdR : (0 : ℝ)≤d := by positivity
  obtain ⟨η,C,P₁,hη,hC,hP₁,hsource⟩ :=
    PolicyCompletionBasicSource.normalized_basic_floor_cutoffs hd hc
      (h := h+δ) (j := j+δ) (b := b-2*δ) (ε := ε/2)
      (by linarith) (by linarith) hphi hb' (half_pos hε) (by linarith)
      (by linarith) (by nlinarith only [hcapPower,hdR,hδ]) (by linarith)
  let P₀ := max P₁ (max (CH^(1/δ)) (max (CJ^(1/δ)) ((2 : ℝ)^(1/h))))
  refine ⟨η,4*C,P₀,hη,by positivity,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP₀ R hR hRup A hA α σ hheight
  have hP₁P : P₁≤P := (le_max_left _ _).trans hP₀
  have hP2 : 2≤P := hP₁.trans hP₁P
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hCHroot : CH^(1/δ)≤P := ((le_max_left _ _).trans (le_max_right _ _)).trans hP₀
  have hCJroot : CJ^(1/δ)≤P :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hP₀
  have hHroot : (2 : ℝ)^(1/h)≤P :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hP₀
  have hCHsmall : CH≤P^δ := fixed_constant_rpow_bound (zero_lt_one.trans_le hCH) hδ hCHroot
  have hCJsmall : CJ≤P^δ := fixed_constant_rpow_bound (zero_lt_one.trans_le hCJ) hδ hCJroot
  have hHpow : 2≤P^h := fixed_constant_rpow_bound (by norm_num) hh hHroot
  have hconduct : P^(3*h+j+(d : ℝ)*phi)≤P^(3*(h+δ)+(j+δ)+(d : ℝ)*phi) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hheight' : P^((d : ℝ)*(b-2*δ)/2)≤height (P^(3*(h+δ)+(j+δ)+(d : ℝ)*phi)) α := by
    calc
      _ ≤ P^((d : ℝ)*b/2) := Real.rpow_le_rpow_of_exponent_le hP1 (by nlinarith only [hdR,hδ])
      _ ≤ height (P^(3*h+j+(d : ℝ)*phi)) α := hheight
      _ ≤ _ := height_mono_conductor (by positivity) hconduct
  have hs := hsource P hP₁P R hR hRup A hA α σ hheight'
  have hm := fixed_dilation_sample_le hP1 hCH hCJ hh hj hδ.le hCHsmall hCJsmall hHpow
    A d 1 phi ((c : ℝ)*α) σ
  apply hm.trans
  calc
    _ ≤ (4*P^(2*δ))*(C*P^(ε/2-(b-2*δ))) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (4*C)*P^(ε/2-b+4*δ) := by
      rw [show 4*P^(2*δ)*(C*P^(ε/2-(b-2*δ)))=(4*C)*(P^(2*δ)*P^(ε/2-(b-2*δ))) by ring]
      rw [← Real.rpow_add hPp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) (by positivity)

theorem normalized_shallow_scaled_cutoffs {k c : ℕ} (hk : 3≤k) (hc : 0<c)
    {CH CJ h j phi b ε : ℝ} (hCH : 1≤CH) (hCJ : 1≤CJ)
    (hh : 0<h) (hj : 0≤j) (hphi : 0<phi) (hb : 0<b) (hε : 0<ε)
    (hcapPhi : b≤phi)
    (hcapError : 2*h+((2*k-2 : ℕ) : ℝ)*phi+b≤j) :
    ∃η C P₀ : ℝ,0<η ∧ 0<C ∧ 2≤P₀ ∧
      ∀P : ℝ,P₀≤P→∀R : ℝ,1≤R→R≤P^η→∀A : Finset ℕ,
      (∀m∈A,P^phi<(m : ℝ) ∧ (m : ℝ)≤P^phi*R)→∀(α : ℝ) (σ : ℕ→ℝ),
      P^((k : ℝ)*b)≤height (P^(3*h+j+((2*k : ℕ) : ℝ)*phi)) α→
      normalizedSampledCoefficient A (2*k) 1 P phi ⌊CH*P^h⌋₊ ⌈CJ*P^j⌉₊ ((c : ℝ)*α) σ≤
        C*P^(ε-b) := by
  let δ := min (b/4) (ε/16)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  have hδb : δ≤b/4 := min_le_left _ _
  have hδε : δ≤ε/16 := min_le_right _ _
  have hb' : 0<b-2*δ := by linarith
  have hkR : (0 : ℝ)≤k := by positivity
  obtain ⟨η,C,P₁,hη,hC,hP₁,hsource⟩ :=
    PolicyCompletionShallowSource.normalized_shallow_floor_cutoffs hk hc
      (h := h+δ) (j := j+δ) (b := b-2*δ) (ε := ε/2)
      (by linarith) (by linarith) hphi hb' (half_pos hε) (by linarith)
      (by linarith)
  let P₀ := max P₁ (max (CH^(1/δ)) (max (CJ^(1/δ)) ((2 : ℝ)^(1/h))))
  refine ⟨η,4*C,P₀,hη,by positivity,hP₁.trans (le_max_left _ _),?_⟩
  intro P hP₀ R hR hRup A hA α σ hheight
  have hP₁P : P₁≤P := (le_max_left _ _).trans hP₀
  have hP2 : 2≤P := hP₁.trans hP₁P
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hCHroot : CH^(1/δ)≤P := ((le_max_left _ _).trans (le_max_right _ _)).trans hP₀
  have hCJroot : CJ^(1/δ)≤P :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hP₀
  have hHroot : (2 : ℝ)^(1/h)≤P :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hP₀
  have hCHsmall : CH≤P^δ := fixed_constant_rpow_bound (zero_lt_one.trans_le hCH) hδ hCHroot
  have hCJsmall : CJ≤P^δ := fixed_constant_rpow_bound (zero_lt_one.trans_le hCJ) hδ hCJroot
  have hHpow : 2≤P^h := fixed_constant_rpow_bound (by norm_num) hh hHroot
  have hconduct : P^(3*h+j+((2*k : ℕ) : ℝ)*phi)≤P^(3*(h+δ)+(j+δ)+((2*k : ℕ) : ℝ)*phi) :=
    Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)
  have hheight' : P^((k : ℝ)*(b-2*δ))≤height (P^(3*(h+δ)+(j+δ)+((2*k : ℕ) : ℝ)*phi)) α := by
    calc
      _ ≤ P^((k : ℝ)*b) := Real.rpow_le_rpow_of_exponent_le hP1 (by nlinarith only [hkR,hδ])
      _ ≤ height (P^(3*h+j+((2*k : ℕ) : ℝ)*phi)) α := hheight
      _ ≤ _ := height_mono_conductor (by positivity) hconduct
  have hs := hsource P hP₁P R hR hRup A hA α σ hheight'
  have hm := fixed_dilation_sample_le hP1 hCH hCJ hh hj hδ.le hCHsmall hCJsmall hHpow
    A (2*k) 1 phi ((c : ℝ)*α) σ
  apply hm.trans
  calc
    _ ≤ (4*P^(2*δ))*(C*P^(ε/2-(b-2*δ))) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (4*C)*P^(ε/2-b+4*δ) := by
      rw [show 4*P^(2*δ)*(C*P^(ε/2-(b-2*δ)))=(4*C)*(P^(2*δ)*P^(ε/2-(b-2*δ))) by ring]
      rw [← Real.rpow_add hPp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith)) (by positivity)

#print axioms normalized_basic_scaled_cutoffs
#print axioms normalized_shallow_scaled_cutoffs
end Waring.PolicyCompletionScaledSource
