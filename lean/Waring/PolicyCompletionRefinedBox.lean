import Waring.PolicyCompletionQuadraticBox
import Waring.FloorCoefficientResources

/-!
# Literal refined coefficient resources on Cartesian floor boxes

The sampled coefficient theorem is applied at exactly the distinguished
height cutoff and the padded product of every other height/ordinary-shift
cutoff. The actual finite tuple average and both floor comparisons are
proved here. The coefficient moment input is genuine admissibility, as in
AnalyticPolicySound, rather than an assumed resource estimate.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionRefinedBox
open CartesianProductSampling CartesianFloorScales CartesianResourceMoments
open ProductMultiplicity NormalizedCoefficient SmoothMoments RationalHeight

theorem product_erase_eq_succAbove {r : ℕ} (b : Fin (r+1) → ℕ)
    (hb : ∀ i, 0 < b i) (i : Fin (r+1)) :
    (∏ l ∈ Finset.univ.erase i, b l) = ∏ l : Fin r, b (i.succAbove l) := by
  apply mul_left_cancel₀ (hb i).ne'
  rw [Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Fin.prod_univ_succAbove b i

theorem coefficient_floor_box_refined {r k power c : ℕ}
    (e : Fin (r+1) → ℝ) (he : ∀ l, 0 < e l) (i : Fin (r+1))
    {T phi Δ ε : ℝ} (hc : 0 < c) (hk : 0 < k) (hpower : 1 ≤ power)
    (hT : T ≤ 1) (hphi : 0 < phi) (hε : 0 < ε)
    (hi : e i=1-(k : ℝ)*phi)
    (htotal : (∑ l, e l)=(k : ℝ)-2-(k : ℝ)*T)
    (hadm : AdmissibleExcess (2*k) (2*power) Δ)
    (hlam : 0 ≤ ((2*power : ℕ) : ℝ)-((2*k : ℕ) : ℝ)+Δ) :
    ∃ η K P₀ : ℝ, 0 < η ∧ 0 < K ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ α ell : ℝ, P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      coefficientBoxMomentAt (floorBounds P e) i A (2*k) power (P^phi) ((c : ℝ)*α) ≤
        K*P^(ε-refinedSaving k T phi ell Δ) := by
  let other : Fin r → ℝ := fun l => e (i.succAbove l)
  have hother : ∀ l, 0 < other l := fun l => he (i.succAbove l)
  have hothers : (∑ l, other l)=(k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi := by
    have hs := Fin.sum_univ_succAbove e i
    rw [htotal,hi] at hs
    change _ = _ + ∑ l, other l at hs
    linarith
  have hj : 0 ≤ (k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi := by
    rw [← hothers]
    exact Finset.sum_nonneg (fun l _ => (hother l).le)
  have hh : 0 < 1-(k : ℝ)*phi := hi ▸ he i
  obtain ⟨η,C,P₁,hη,hC,hP₁,hrefined⟩ := normalized_refined_floor_cutoffs
    (CH := 1) (CJ := 1) hc (by norm_num) (by norm_num) hk hpower hT hphi
    (half_pos hε) hh hj hadm hlam
  let B : ℝ := (∑ l, other l)+1
  have hB : 0 ≤ B := by
    have hs0 : 0 ≤ ∑ l, other l := Finset.sum_nonneg (fun l _ => (hother l).le)
    dsimp [B]
    linarith
  obtain ⟨D,hD,hbox⟩ := coefficient_box_at_to_sample r hB (half_pos hε)
  let P₀ := max P₁ (coordinateThreshold e)
  refine ⟨η,D*(2 : ℝ)^(r+1)*C,P₀,hη,by positivity,hP₁.trans (le_max_left _ _),?_⟩
  intro P hPP₀ R hR hRup A hA α ell hheight
  have hP₁P : P₁ ≤ P := (le_max_left _ _).trans hPP₀
  have hPe : coordinateThreshold e ≤ P := (le_max_right _ _).trans hPP₀
  have hP2 := hP₁.trans hP₁P
  have hP1 : 1 ≤ P := by linarith
  have hPp : 0 < P := by linarith
  have hpow := coordinate_powers_ge_two e he hPe
  have hbpos := floorBounds_pos e hpow
  have hpowother : ∀ l, 2 ≤ P^(other l) := fun l => hpow (i.succAbove l)
  let J := paddedCutoff P other
  have hprod : (∏ l ∈ Finset.univ.erase i, floorBounds P e l)=actualVolume P other := by
    rw [product_erase_eq_succAbove _ hbpos i]
    rfl
  have hVJ : (∏ l ∈ Finset.univ.erase i, floorBounds P e l) ≤ J := by
    rw [hprod]
    exact actualVolume_le_paddedCutoff other (fun l => (hother l).le) hPp.le hpowother
  have hpad : (J : ℝ) ≤ (2 : ℝ)^(r+1)*
      ((∏ l ∈ Finset.univ.erase i, floorBounds P e l : ℕ) : ℝ) := by
    rw [hprod]
    exact paddedCutoff_le_actualVolume other (fun l => (hother l).le) hP1 hpowother
  have hJup : (J : ℝ) ≤ P^B := by
    calc
      _ ≤ 2*P^(∑ l, other l) := paddedCutoff_le_twice_power other
        (fun l => (hother l).le) hP1
      _ ≤ P*P^(∑ l, other l) := mul_le_mul_of_nonneg_right hP2
        (Real.rpow_nonneg hPp.le _)
      _ = P^B := by
        calc
          _ = P^(1 : ℝ)*P^(∑ l, other l) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hPp]; congr 1; dsimp [B]; ring
  have hHdef : floorBounds P e i=⌊P^(1-(k : ℝ)*phi)⌋₊ := by
    simp only [floorBounds,hi]
  have hJdef : J=⌈P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)⌉₊ := by
    simp only [J,paddedCutoff,hothers]
  have hn := hrefined P hP₁P R hR hRup A hA α ell (fun _ => 1) hheight
  simp only [one_mul] at hn
  rw [← hHdef,← hJdef] at hn
  have hb := hbox P hP1 (floorBounds P e) hbpos i J hVJ hJup
    ((2 : ℝ)^(r+1)) hpad A (2*k) power phi ((c : ℝ)*α)
  apply hb.trans
  calc
    _ ≤ D*(2 : ℝ)^(r+1)*P^(ε/2)*(C*P^(ε/2-refinedSaving k T phi ell Δ)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (D*(2 : ℝ)^(r+1)*C)*P^(ε-refinedSaving k T phi ell Δ) := by
      have hp : P^(ε/2)*P^(ε/2-refinedSaving k T phi ell Δ)=
          P^(ε-refinedSaving k T phi ell Δ) := by
        rw [← Real.rpow_add hPp]
        congr 1
        ring
      calc
        _ = (D*(2 : ℝ)^(r+1)*C)*(P^(ε/2)*P^(ε/2-refinedSaving k T phi ell Δ)) := by ring
        _ = _ := by rw [hp]

#print axioms coefficient_floor_box_refined
end Waring.PolicyCompletionRefinedBox
