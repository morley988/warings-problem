import Waring.PolicyCompletionQuadraticBox
import Waring.PolicyCompletionScaledBounds

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledQuadraticBox
open PolicyCompletionQuadraticBox PolicyCompletionScaledBounds
open CartesianProductSampling CartesianFloorScales CartesianResourceMoments
open NormalizedQuadratic RationalHeight NormalizedCoefficient
open ProductMultiplicity FiniteResourceHolder CoefficientFactorization

/-- A complete z2 resource for the actual floor box, allowing the fixed
support enlargement needed by completed quadratic source sums. -/
theorem quadratic_floor_box_second {r : ℕ} (Dscale : ℝ) (hDscale : 1≤Dscale) (e : Fin r → ℝ)
    (he : ∀ i, 0 < e i) (hsum : 1 < ∑ i, e i)
    (rho L : ℝ) (hrho : 0 ≤ rho) (hL : 1 ≤ L) (c : ℕ) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ (α t : ℝ) (S : Finset ℤ), (∀ z ∈ S, |(z : ℝ)| ≤ L*P) →
      P/R^rho ≤ height (P^((∑ i, e i)+2)) α →
      quadraticBoxMoment (scaledBounds Dscale P e) S P α t c 2 ≤ K*P^(ε-1) := by
  let E := ∑ i, e i
  have hE : 1 < E := hsum
  have hA : 0 ≤ E+1 := by linarith
  have hLp : 0 < L := zero_lt_one.trans_le hL
  obtain ⟨η,C,P₁,hη,hC,hP₁,hsample⟩ := normalized_second_fixed_support
    (E+1) rho L hA hrho hL c hc (half_pos hε)
  obtain ⟨D,hD,hbox⟩ := quadratic_second_box_to_sample r (B := E+1) hA (half_pos hε)
  obtain ⟨P₂,hP₂,hscales⟩ := eventual_scaled_scales Dscale hDscale e he
  let P₀ := max (max 2 P₁) (max P₂ (L^(1/(E-1))))
  refine ⟨η,D*(2 : ℝ)^(r+1)*C,P₀,hη,by positivity,
    (le_max_left 2 P₁).trans (le_max_left _ _),?_⟩
  intro P hPP₀ R hR hRup α t S hS hheight
  have hP2 : 2 ≤ P := ((le_max_left 2 P₁).trans (le_max_left _ _)).trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPp : 0 < P := by linarith
  have hP₁P : P₁ ≤ P := ((le_max_right 2 P₁).trans (le_max_left _ _)).trans hPP₀
  have hP₂P : P₂ ≤ P := ((le_max_left P₂ _).trans (le_max_right _ _)).trans hPP₀
  have hLbound : L^(1/(E-1)) ≤ P :=
    ((le_max_right P₂ _).trans (le_max_right _ _)).trans hPP₀
  have hLsmall : L ≤ P^(E-1) := fixed_constant_rpow_bound hLp (by linarith) hLbound
  let J := scaledCutoff Dscale P e
  have hs := hscales P hP₂P
  have hPJ : L*P ≤ (J : ℝ) := by
    calc
      _ ≤ P^(E-1)*P := mul_le_mul_of_nonneg_right hLsmall hPp.le
      _ = P^E := by
        calc
          _ = P^(E-1)*P^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hPp]; congr 1; ring
      _ ≤ Dscale^r*P^E := le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) (one_le_pow₀ hDscale)
      _ ≤ _ := Nat.le_ceil _
  have hJup : (J : ℝ) ≤ P^(E+1) := hs.2.2.2.2.2
  have hJphys : (J : ℝ) ≤ (L*P)^(E+1) := hJup.trans
    (Real.rpow_le_rpow hPp.le (le_mul_of_one_le_left hPp.le hL) hA)
  have hconduct : P^(E+2) ≤ (J : ℝ)*P^2 := by
    have hbase : P^E≤(J : ℝ) :=
      (le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) (one_le_pow₀ hDscale)).trans
        (Nat.le_ceil (Dscale^r*P^E))
    have hh := mul_le_mul_of_nonneg_right hbase (sq_nonneg P)
    simpa only [Real.rpow_add hPp,Real.rpow_two,J,scaledCutoff,E] using hh
  have hJpos : (0 : ℝ) < J := (mul_pos hLp hPp).trans_le hPJ
  have hheight' : P/R^rho ≤ height ((J : ℝ)*P^2) α :=
    hheight.trans (height_mono_conductor (by positivity) hconduct)
  have hb := hbox P hP1 (scaledBounds Dscale P e) hs.1 J hs.2.2.2.1 hJup
    ((2 : ℝ)^(r+1)) hs.2.2.2.2.1 S α t c
  have hn := hsample P hP₁P R hR hRup J hPJ hJphys α t S hS hheight'
  apply hb.trans
  calc
    _ ≤ D*(2 : ℝ)^(r+1)*P^(ε/2)*(C*P^(ε/2-1)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (D*(2 : ℝ)^(r+1)*C)*P^(ε-1) := by
      have hp : P^(ε/2)*P^(ε/2-1)=P^(ε-1) := by
        rw [← Real.rpow_add hPp]
        congr 1
        ring
      calc
        _ = (D*(2 : ℝ)^(r+1)*C)*(P^(ε/2)*P^(ε/2-1)) := by ring
        _ = _ := by rw [hp]

#print axioms quadratic_floor_box_second
end Waring.PolicyCompletionScaledQuadraticBox
