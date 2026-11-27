import Waring.PhysicalCoefficientResources
import Waring.CartesianFloorScales

/-!
# Literal floor and padded-ceiling coefficient cutoffs

The hypotheses about physical sampling scales are discharged for the actual
cutoffs floor(CH*P^(1-k*phi)) and ceil(CJ*P^(k-3-k*T+k*phi)). Fixed source
normalizations CH,CJ are retained. No conductor or cutoff comparison premise
remains, and the height is the original common height.
-/

noncomputable section
namespace Waring.NormalizedCoefficient
open CoefficientPower SmoothMoments RationalHeight

/-- Refined saving for the literal integer cutoffs with all fixed factors absorbed. -/
theorem normalized_refined_floor_cutoffs {k r c : ℕ} {T phi Δ ε CH CJ : ℝ}
    (hc : 0 < c) (hCH : 1 ≤ CH) (hCJ : 1 ≤ CJ)
    (hk : 0 < k) (hr : 1 ≤ r) (hT : T ≤ 1) (hphi : 0 < phi) (hε : 0 < ε)
    (hh : 0 < 1-(k : ℝ)*phi) (hj : 0 ≤ (k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ (α ell : ℝ) (σ : ℕ → ℝ), P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      normalizedSampledCoefficient A (2*k) r P phi
        ⌊CH*P^(1-(k : ℝ)*phi)⌋₊ ⌈CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)⌉₊
        ((c : ℝ)*α) σ ≤ C*P^(ε-refinedSaving k T phi ell Δ) := by
  have hCJ2 : 1 ≤ 2*CJ := by linarith
  obtain ⟨η,C,P₀,hη,hC,hP₀,hbound⟩ := normalized_refined_physical
    (CHlo := 2) (CHup := CH) (CJlo := 1) (CJup := 2*CJ) (T := T)
    hc (by norm_num) hCH (by norm_num) hCJ2 hk hr hT hphi hε hadm hlam
  refine ⟨η,C,max P₀ ((2 : ℝ)^(1/(1-(k : ℝ)*phi))),hη,hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA α ell σ hL
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hpow : 2 ≤ P^(1-(k : ℝ)*phi) := fixed_constant_rpow_bound (by norm_num) hh
    ((le_max_right _ _).trans hP₀')
  have hCHp : P^(1-(k : ℝ)*phi) ≤ CH*P^(1-(k : ℝ)*phi) :=
    le_mul_of_one_le_left (Real.rpow_nonneg hPpos.le _) hCH
  have hHbase : 2 ≤ CH*P^(1-(k : ℝ)*phi) := hpow.trans hCHp
  have hHlo := CartesianFloorScales.half_le_floor hHbase
  have hHup := Nat.floor_le (show 0 ≤ CH*P^(1-(k : ℝ)*phi) by positivity)
  have hHpos : 0 < ⌊CH*P^(1-(k : ℝ)*phi)⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hjpow : 1 ≤ P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) := Real.one_le_rpow hP1 hj
  have hCJp : P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) ≤
      CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) :=
    le_mul_of_one_le_left (Real.rpow_nonneg hPpos.le _) hCJ
  have hJbase : 1 ≤ CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) := hjpow.trans hCJp
  have hJlo := Nat.le_ceil (CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi))
  have hJup := CartesianFloorScales.ceil_le_twice hJbase
  have hJpos : 0 < ⌈CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)⌉₊ :=
    Nat.ceil_pos.mpr (zero_lt_one.trans_le hJbase)
  apply hbound P hPP₀ R hR hRup A hA _ _ hHpos hJpos
  · nlinarith only [hHlo,hCHp]
  · exact hHup
  · simpa only [one_mul] using hCJp.trans hJlo
  · nlinarith only [hJup]
  · exact hL

/-- Cube saving for the same literal integer cutoffs. -/
theorem normalized_cube_floor_cutoffs {k r c : ℕ} {T phi Δ ε CH CJ : ℝ}
    (hc : 0 < c) (hCH : 1 ≤ CH) (hCJ : 1 ≤ CJ)
    (hk : 0 < k) (hr : 1 ≤ r) (hT : T ≤ 1) (hphi : 0 < phi) (hε : 0 < ε)
    (hh : 0 < 1-(k : ℝ)*phi) (hj : 0 ≤ (k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ (α ell : ℝ) (σ : ℕ → ℝ), P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      normalizedSampledCoefficient A (2*k) r P phi
        ⌊CH*P^(1-(k : ℝ)*phi)⌋₊ ⌈CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)⌉₊
        ((c : ℝ)*α) σ ≤ C*P^(ε-cubeSaving k T phi ell Δ) := by
  have hCJ2 : 1 ≤ 2*CJ := by linarith
  obtain ⟨η,C,P₀,hη,hC,hP₀,hbound⟩ := normalized_cube_physical
    (CHlo := 2) (CHup := CH) (CJlo := 1) (CJup := 2*CJ) (T := T)
    hc (by norm_num) hCH (by norm_num) hCJ2 hk hr hT hphi hε hadm hlam
  refine ⟨η,C,max P₀ ((2 : ℝ)^(1/(1-(k : ℝ)*phi))),hη,hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA α ell σ hL
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hpow : 2 ≤ P^(1-(k : ℝ)*phi) := fixed_constant_rpow_bound (by norm_num) hh
    ((le_max_right _ _).trans hP₀')
  have hCHp : P^(1-(k : ℝ)*phi) ≤ CH*P^(1-(k : ℝ)*phi) :=
    le_mul_of_one_le_left (Real.rpow_nonneg hPpos.le _) hCH
  have hHbase : 2 ≤ CH*P^(1-(k : ℝ)*phi) := hpow.trans hCHp
  have hHlo := CartesianFloorScales.half_le_floor hHbase
  have hHup := Nat.floor_le (show 0 ≤ CH*P^(1-(k : ℝ)*phi) by positivity)
  have hHpos : 0 < ⌊CH*P^(1-(k : ℝ)*phi)⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hjpow : 1 ≤ P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) := Real.one_le_rpow hP1 hj
  have hCJp : P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) ≤
      CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) :=
    le_mul_of_one_le_left (Real.rpow_nonneg hPpos.le _) hCJ
  have hJbase : 1 ≤ CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) := hjpow.trans hCJp
  have hJlo := Nat.le_ceil (CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi))
  have hJup := CartesianFloorScales.ceil_le_twice hJbase
  have hJpos : 0 < ⌈CJ*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi)⌉₊ :=
    Nat.ceil_pos.mpr (zero_lt_one.trans_le hJbase)
  apply hbound P hPP₀ R hR hRup A hA _ _ hHpos hJpos
  · nlinarith only [hHlo,hCHp]
  · exact hHup
  · simpa only [one_mul] using hCJp.trans hJlo
  · nlinarith only [hJup]
  · exact hL

#print axioms normalized_refined_floor_cutoffs
#print axioms normalized_cube_floor_cutoffs
end Waring.NormalizedCoefficient
