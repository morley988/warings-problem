import Waring.SeedCompletionTerminalDivisorReal
import Waring.PolicyCompletionSharpResidualDivisorBox

/-! # Sharp actual divisor terminals on real parameter boxes -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSharpDivisorReal
open SeedCompletionTerminalSparse SeedCompletionTerminalDivisorReal
open SeedCompletionDivisorEnlargement AuxiliaryCounting AuxiliaryTupleCount
open PolicyCompletionSharpResidualDivisorBox PolicyCompletionSharpResidualSource

theorem sharp_padded_second_moment_divisor_real_box {k j r : ℕ} (hk : k≤18)
    (hjk : j+r+2≤k) (hj : 1≤j) (hgood : SharpResidual k (j+r)) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∃ P₀ : ℝ, 2≤P₀ ∧ ∀ P : ℝ, P₀≤P →
      ∀ R : ℝ, 1≤R → R≤P → ∀ (Hcap M : ℕ→ℝ),
      (∀ i<j,1≤Hcap i ∧ Hcap i≤P) →
      (∀ i<j,1≤M i ∧ M i≤P) →
      (∀ i<j,(∏ l ∈ Finset.range i,M l)≤Hcap i*M i) →
      ∀ (H A : Fin j→Finset ℕ) (G : Fin r→Finset ℕ),
      (∀ i,∀ h∈H i,0<h ∧ (h:ℝ)≤Hcap i.val) →
      (∀ i,∀ m∈A i,0<m ∧ (m:ℝ)≤M i.val*R) →
      (∀ i,∀ h∈G i,0<h ∧ (h:ℝ)≤P) →
      ∀ Z : Finset ℕ, (∀ z∈Z,0<z ∧ (z:ℝ)≤P) → (Z.card:ℝ)≤P →
      paddedSecondMoment k H A G Z≤C*P^ε*swellFactor j R*
        (P+(∏ i : Fin j,M i.val*R))*
        (∏ i : Fin j,Hcap i.val)*(∏ i : Fin j,M i.val*R)*
        ((Fintype.piFinset G).card:ℝ) := by
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := sharp_padded_second_moment_divisor_box hk hjk hj hgood
    (B:=((2*j+3:ℕ):ℝ)) (L:=(((2*j+3)*(2+2*k):ℕ):ℝ))
    (by exact_mod_cast (show 1≤2*j+3 by omega)) (by positivity) hε
  refine ⟨C,hC,max P₀ 2,le_max_right _ _,?_⟩
  intro P hPP R hR hRP Hcap M hHcap hM hprefix H A G hH hA hG Z hZ hZcard
  have hP2 : 2≤P := (le_max_right P₀ 2).trans hPP
  have hP1 : 1≤P := by linarith
  have hPP₀ : P₀≤P := (le_max_left P₀ 2).trans hPP
  have hpowers := inflated_polynomial_bounds hP2 hR hRP Hcap M hHcap hM
  have hsizes := inflated_size (k:=k) hP2 hR hRP Hcap M hHcap hM
  have hparams := inflated_prefix hR Hcap M (fun i hi=>(hHcap i hi).1)
    (fun i hi=>(hM i hi).1) hprefix
  have hb := hbound P hPP₀ H A G (inflatedHeight j R Hcap) (inflatedCoefficient R M)
    (by
      intro i h hh
      have hh := hH i h hh
      refine Finset.mem_Icc.mpr ⟨hh.1,?_⟩
      have hu := hh.2.trans (inflatedHeight_bounds (j:=j) hR Hcap (hHcap i.val i.isLt).1).1
      exact_mod_cast hu)
    (by
      intro i m hm
      have hm := hA i m hm
      refine Finset.mem_Icc.mpr ⟨hm.1,?_⟩
      have hu := hm.2.trans (inflatedCoefficient_bounds hR M (hM i.val i.isLt).1).1
      exact_mod_cast hu)
    (by simpa only [Real.rpow_natCast] using hpowers)
    (by simpa only [Real.rpow_natCast] using hsizes) hparams
    (by
      intro i h hh
      have hh := hG i h hh
      refine ⟨hh.1,hh.2.trans ?_⟩
      simpa only [Real.rpow_natCast] using
        (le_self_pow₀ hP1 (show 2*j+3≠0 by omega))) Z hZ hZcard
  have hQ := inflated_coefficient_volume hR M (fun i hi=>(hM i hi).1)
  have hD := inflated_diagonal_volume hR Hcap M (fun i hi=>(hHcap i hi).1)
    (fun i hi=>(hM i hi).1)
  have hMprod : 0≤∏ i : Fin j,M i.val*R := Finset.prod_nonneg (by
    intro i _
    have hi := (hM i.val i.isLt).1
    positivity)
  have hHprod : 0≤∏ i : Fin j,Hcap i.val := Finset.prod_nonneg (by
    intro i _
    linarith [(hHcap i.val i.isLt).1])
  have hcurve : P+((coordinateBox (inflatedCoefficient R M) j).card:ℝ)≤
      2^j*(P+(∏ i : Fin j,M i.val*R)) := by
    have htwo : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
    have hp : P≤2^j*P := le_mul_of_one_le_left (by linarith) htwo
    nlinarith [hQ]
  apply hb.trans
  calc
    _ ≤ C*P^ε*(2^j*(P+(∏ i : Fin j,M i.val*R)))*
        ((4*(2*R)^j)^j*(∏ i : Fin j,Hcap i.val)*(∏ i : Fin j,M i.val*R))*
        ((Fintype.piFinset G).card:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcurve (by positivity)) hD
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by unfold swellFactor; ring

#print axioms sharp_padded_second_moment_divisor_real_box
end Waring.SeedCompletionSharpDivisorReal
