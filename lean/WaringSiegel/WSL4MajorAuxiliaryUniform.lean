import WaringSiegel.WSL4MajorAuxiliaryBroad
import WaringSiegel.WSL4MajorAuxiliaryErrors

/-! # Uniform auxiliary major asymptotics for a growing prime -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliaryMajorCoefficient_uniform_approximation
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (C0 : ℝ) (hC0 : 1≤C0)
    (δ : ℝ) (hδ : δ<5/48) (c : ℝ) (hc : 0<c) :
    ∃ X0 : ℝ, 1≤X0 ∧ ∀ (target : 𝓞 K) (htarget : target≠0),
      X0<(rootScale 3 target)^finrank ℚ K →
      ∀ (p : ℕ) (hp : p.Prime), 173≤p →
      (p:ℝ)^finrank ℚ K≤((rootScale 3 target)^finrank ℚ K)^δ →
      ‖auxiliaryMajorCoefficient ρ R hρ hR (rootScale 3 target) (rootScale_pos htarget 3)
          p hp.pos (C0*(rootScale 3 target)^finrank ℚ K) target-
        (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
          (auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
              (smoothRootWeight ρ R) (normalizedTarget 3 1 target))‖ ≤
        c*auxiliaryMajorScale (K := K) (rootScale 3 target) p := by
  obtain ⟨N,hN⟩ := exists_auxiliary_poisson_order δ (by linarith)
  obtain ⟨C₁,C₂,C₃,hC₁,hC₂,hC₃,hbound⟩ :=
    broadAuxiliaryCoefficient_full_main_error (K := K) ρ R hρ hR C0 hC0 N
  obtain ⟨M,hM,herror⟩ := exists_auxiliary_relative_error_small δ C₁ C₂ C₃ c
    hδ hC₁.le hC₂.le hC₃.le hc N hN
  let D : ℝ := (FractionalIdeal.absNorm (inverseDifferent K):ℝ)
  have hD : 0<D := fractionalIdeal_absNorm_pos _ inverseDifferent_ne_zero
  let T := max M ((2:ℝ)^finrank ℚ K*C0^2/D+1)
  refine ⟨T,hM.trans (le_max_left _ _),?_⟩
  intro target htarget hTX p hp hp173 hYX
  let P := rootScale 3 target
  let X := P^finrank ℚ K
  let Y := (p:ℝ)^finrank ℚ K
  let L := X^((4:ℝ)/5)
  let z := auxiliaryMajorScale (K := K) P p
  have hP : 0<P := rootScale_pos htarget 3
  have hX1 : 1≤X := (hM.trans (le_max_left _ _)).trans hTX.le
  have hX : 0<X := lt_of_lt_of_le zero_lt_one hX1
  have hY : 0<Y := pow_pos (Nat.cast_pos.mpr hp.pos) _
  have hz : 0<z := auxiliaryMajorScale_pos (K := K) P hP p hp.pos
  obtain ⟨hratio,herr⟩ := herror X Y ((le_max_left _ _).trans_lt hTX) hY.le hYX
  have hL1 : 1≤L := Real.one_le_rpow hX1 (by norm_num)
  have hYL : Y*L≤X := (div_le_one hX).mp hratio
  have hYleX : Y≤X := hYX.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX1
      (show δ≤1 by linarith))
  have hpP : (p:ℝ)≤P := by
    by_contra h
    have hh := pow_lt_pow_left₀ (lt_of_not_ge h) hP.le
      (Nat.ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
    exact not_lt_of_ge hYleX hh
  have hPp : 1≤P/(p:ℝ) := (one_le_div (Nat.cast_pos.mpr hp.pos)).mpr hpP
  have hcoef : (2:ℝ)^finrank ℚ K*C0^2<D*X := by
    rw [mul_comm D X]
    apply (div_lt_iff₀ hD).mp
    have hh := (le_max_right M ((2:ℝ)^finrank ℚ K*C0^2/D+1)).trans_lt hTX
    linarith
  have hpow : (P^3)^finrank ℚ K=X^3 := by
    dsimp [X]
    rw [← pow_mul,← pow_mul,Nat.mul_comm 3]
  have hsep : (2:ℝ)^finrank ℚ K*(C0*X)^2<D*(P^3)^finrank ℚ K := by
    rw [hpow]
    calc
      _ = ((2:ℝ)^finrank ℚ K*C0^2)*X^2 := by ring
      _ < (D*X)*X^2 := mul_lt_mul_of_pos_right hcoef (pow_pos hX 2)
      _ = _ := by ring
  have he := hbound target htarget p hp hp173 hPp L hL1 hYL hsep
  have hlength : (P/(p:ℝ))^finrank ℚ K=X/Y := by dsimp [X,Y]; rw [div_pow]
  have hY2 : (p:ℝ)^(2*finrank ℚ K)=Y^2 := by
    dsimp [Y]
    rw [← pow_mul,Nat.mul_comm 2]
  have hvol : X^4*((P/(p:ℝ))^finrank ℚ K)^4=z*X^3 := by
    rw [hlength,div_pow]
    change X^4*(X^4/Y^4)=(X^5/Y^4)*X^3
    ring
  have hzy : z*Y^4=X^5 := div_mul_cancel₀ _ (pow_ne_zero _ hY.ne')
  have hfactor : C₁*X^4*((P/(p:ℝ))^finrank ℚ K)^4*(Y*L/X)^N +
      z*C₂*(p:ℝ)^(2*finrank ℚ K)/L^((5:ℝ)/4) +
      C₃*X^5*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) =
      z*(C₁*X^3*(Y*L/X)^N + C₂*Y^2/L^((5:ℝ)/4) +
        C₃*Y^4*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4))) := by
    rw [hY2]
    calc
      _ = C₁*(X^4*((P/(p:ℝ))^finrank ℚ K)^4)*(Y*L/X)^N +
          z*C₂*Y^2/L^((5:ℝ)/4) +
          C₃*(z*Y^4)*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) := by rw [hzy]; ring
      _ = _ := by rw [hvol]; ring
  change ‖_‖≤C₁*X^4*((P/(p:ℝ))^finrank ℚ K)^4*(Y*L/X)^N +
    z*C₂*(p:ℝ)^(2*finrank ℚ K)/L^((5:ℝ)/4) +
    C₃*X^5*(1/L^((5:ℝ)/4)+Y^8/X^((5:ℝ)/4)) at he
  rw [hfactor] at he
  exact (he.trans_lt (mul_lt_mul_of_pos_left herr hz)).le.trans_eq (mul_comm z c)

#print axioms auxiliaryMajorCoefficient_uniform_approximation
end WaringSiegel.WSL4
