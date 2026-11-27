import Waring.PolicyCompletionFourthBox
import Waring.PolicyCompletionScaledBounds

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledFourthSample
open RationalHeight NormalizedQuadratic CartesianProductSampling
open CartesianResourceMoments CartesianFloorScales ProductMultiplicity
open CartesianPolynomialBounds PolicyCompletionFourthBox

theorem fourth_shape_refined_fixed {P H L ell h D : ℝ} (hD : 1≤D)
    (hP : 1≤P) (hH : 0≤H) (hL : 0<L) (hHs : H≤D*P^h) (hLs : P^ell≤L) :
    H*P^2+P^4*min (H/L) (H^2/L^2)≤(2*D)*H*P^4*P^(-z4RefinedSaving ell h) := by
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hcap : z4RefinedSaving ell h≤2*ell-h := min_le_right _ _
  have hcap2 : z4RefinedSaving ell h≤2 := min_le_left _ _
  have hden : P^(2*ell)≤L^2 := by
    calc
      _ = (P^ell)^2 := by rw [← Real.rpow_mul_natCast hPp.le]; congr 1; norm_num; ring
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hPp.le _) hLs 2
  have hratio : H/L^2≤D*P^(-(2*ell-h)) := by
    calc
      _ ≤ (D*P^h)/P^(2*ell) := div_le_div₀ (by positivity) hHs (Real.rpow_pos_of_pos hPp _) hden
      _ = _ := by rw [mul_div_assoc,← Real.rpow_sub hPp]; congr 2; ring
  have hmin : min (H/L) (H^2/L^2)≤D*H*P^(-z4RefinedSaving ell h) := by
    calc
      _ ≤ H^2/L^2 := min_le_right _ _
      _ = H*(H/L^2) := by ring
      _ ≤ H*(D*P^(-(2*ell-h))) := mul_le_mul_of_nonneg_left hratio hH
      _ ≤ H*(D*P^(-z4RefinedSaving ell h)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcap))
            (by linarith)) hH
      _ = _ := by ring
  have hfirst : H*P^2≤H*P^4*P^(-z4RefinedSaving ell h) := by
    have hid : P^2=P^4*P^(-2 : ℝ) := by
      rw [Real.rpow_neg hPp.le]
      norm_num only [Real.rpow_ofNat]
      field_simp
    calc
      _ = (H*P^4)*P^(-2 : ℝ) := by rw [hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcap2)) (by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hmin (show 0≤P^4 by positivity)
  have hnon : 0≤H*P^4*P^(-z4RefinedSaving ell h) := by positivity
  nlinarith only [hfirst,hsecond,hnon,hD]

theorem normalized_fourth_fixed_dilations (Lscale Hscale : ℝ)
    (hLscale : 1≤Lscale) (hHscale : 1≤Hscale) (B : ℝ) (hB : 0≤B) (c : ℕ) (hc : 0<c)
    {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,2≤P→∀H : ℝ,1≤H→H≤P^B→
      ∀α ell h : ℝ,H≤Hscale*P^h→P^ell≤height (H*P^2) α→
      ∀s : Finset ℕ,∀a b : ℕ→ℤ,∀t : ℕ→ℝ,
      (∀q∈s,0<q ∧ (q : ℝ)≤H)→(∀q∈s,a q≤b q)→
      (∀q∈s,(((b q+1-a q).toNat : ℕ) : ℝ)≤Lscale*P)→
      normalizedFourth s a b t c P H α≤C*P^(ε-z4Saving ell h) ∧
      normalizedFourth s a b t c P H α≤C*P^(ε-z4RefinedSaving ell h) := by
  obtain ⟨Cs,hCs,hbound⟩ := SampledQuadraticAsymptotic.sampled_fourth_moment_epsilon B hB c hc hε
  let C := Lscale^4*Cs*Lscale^ε
  have hLsp : 0<Lscale := zero_lt_one.trans_le hLscale
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨(2+2*Hscale)*C,by positivity,?_⟩
  intro P hP H hH hHB α ell h hHs hLs s a b t hs hab hlength
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hHp : 0<H := zero_lt_one.trans_le hH
  have hPX : P≤Lscale*P := le_mul_of_one_le_left hPp.le hLscale
  have hX : 2≤Lscale*P := hP.trans hPX
  have hHX : H≤(Lscale*P)^B := hHB.trans (Real.rpow_le_rpow hPp.le hPX hB)
  have hraw := hbound (Lscale*P) hX H hH hHX α s a b t hs hab hlength
  let L := height (H*(Lscale*P)^2) α
  have hLp : 0<L := height_pos _ _
  have hLL : P^ell≤L := hLs.trans (height_mono_conductor (by positivity) (by gcongr))
  have hraw' : (∑q∈s,‖∑z∈Finset.Icc (a q) (b q),
      QuadraticModulation.e ((c : ℝ)*((q : ℝ)*α)*(z : ℝ)^2+t q*z)‖^4)≤
      C*P^ε*(H*P^2+P^4*min (H/L) (H^2/L^2)) := by
    apply hraw.trans
    have hscale : H*(Lscale*P)^2+(Lscale*P)^4*min (H/L) (H^2/L^2)≤
        Lscale^4*(H*P^2+P^4*min (H/L) (H^2/L^2)) := by
      have hl : Lscale^2≤Lscale^4 := pow_le_pow_right₀ hLscale (by omega)
      calc
        _ = Lscale^2*(H*P^2)+Lscale^4*(P^4*min (H/L) (H^2/L^2)) := by ring
        _ ≤ Lscale^4*(H*P^2)+Lscale^4*(P^4*min (H/L) (H^2/L^2)) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hl (by positivity)) _
        _ = _ := by ring
    calc
      _ ≤ Cs*(Lscale*P)^ε*(Lscale^4*(H*P^2+P^4*min (H/L) (H^2/L^2))) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by rw [Real.mul_rpow hLsp.le hPp.le]; dsimp [C]; ring
  constructor
  · have hh := normalize_fourth_shape hPp hHp hC.le hraw'
      (fourth_shape_old (h := h) hP1 hHp.le hLp hLL)
    exact hh.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hHscale,hC] : 2*C≤(2+2*Hscale)*C)
      (Real.rpow_nonneg hPp.le _))
  · have hh := normalize_fourth_shape hPp hHp hC.le hraw'
      (fourth_shape_refined_fixed hHscale hP1 hHp.le hLp hHs hLL)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by nlinarith : (2*Hscale)*C≤(2+2*Hscale)*C) (Real.rpow_nonneg hPp.le _))

#print axioms fourth_shape_refined_fixed
#print axioms normalized_fourth_fixed_dilations
end Waring.PolicyCompletionScaledFourthSample
