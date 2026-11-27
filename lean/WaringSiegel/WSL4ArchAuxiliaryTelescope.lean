import WaringSiegel.WSL4ArchAuxiliaryTrivial

/-! # An actual eight-factor auxiliary Poisson replacement -/
noncomputable section
set_option maxHeartbeats 1700000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem norm_fourth_sub_fourth_le (z w : ℂ) {A E : ℝ} (hA : 0≤A) (hE : 0≤E)
    (hz : ‖z‖≤A) (hw : ‖w‖≤A) (hd : ‖z-w‖≤E) :
    ‖z^4-w^4‖≤4*A^3*E := by
  have hh : ‖z^4-w^4‖≤4*A^3*‖z-w‖ := by
    simpa only [Nat.reduceAdd,Nat.cast_ofNat,show (3:ℝ)+1=4 by norm_num] using
      complex_norm_pow_sub_pow hA hz hw 3
  exact hh.trans (mul_le_mul_of_nonneg_left hd (by positivity))

theorem norm_four_by_four_sub_le (f g a b : ℂ) {X Z EF EG : ℝ}
    (hX : 0≤X) (hZ : 0≤Z) (hEF : 0≤EF) (hEG : 0≤EG)
    (hf : ‖f‖≤X) (ha : ‖a‖≤X) (hg : ‖g‖≤Z) (hb : ‖b‖≤Z)
    (hfa : ‖f-a‖≤EF) (hgb : ‖g-b‖≤EG) :
    ‖f^4*g^4-a^4*b^4‖≤4*X^3*EF*Z^4+X^4*(4*Z^3*EG) := by
  have hdf := norm_fourth_sub_fourth_le f a hX hEF hf ha hfa
  have hdg := norm_fourth_sub_fourth_le g b hZ hEG hg hb hgb
  calc
    _ = ‖(f^4-a^4)*g^4+a^4*(g^4-b^4)‖ := by congr 1; ring
    _ ≤ ‖(f^4-a^4)*g^4‖+‖a^4*(g^4-b^4)‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul,norm_pow]
      exact add_le_add
        (mul_le_mul hdf (pow_le_pow_left₀ (norm_nonneg _) hg 4) (by positivity) (by positivity))
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha 4) hdg (norm_nonneg _) (by positivity))

theorem auxiliary_root_eightfold_main_error (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : 0<p) (P : ℝ) (hP : 0<P)
      (hsmall : 1≤P/(p:ℝ)) (β : mixedSpace K), auxiliaryRootArcRatio P p γ β≤1 →
    ‖(compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
          (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0)^4 *
        (smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
          (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β))))^4 -
      (auxiliaryRootMaskedMain rho R P γ p (Nat.ne_of_gt hp) β)^4 *
        (auxiliaryRootScaledMain rho R P γ p β)^4‖ ≤
      C*(P^finrank ℚ K)^4*((P/(p:ℝ))^finrank ℚ K)^4*(auxiliaryRootArcRatio P p γ β)^N := by
  obtain ⟨CT,hCT,ht⟩ := auxiliary_root_sources_trivial_bound (K:=K) rho R hrho hR
  obtain ⟨CF,hCF,hf⟩ := auxiliaryRootMaskedSource_main_error (K:=K) rho R hrho hR N
  obtain ⟨CG,hCG,hg⟩ := auxiliaryRootScaledSource_main_error (K:=K) rho R hrho hR N
  let D := CT+2*CF+2*CG
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨8*D^7*(CF+CG),by positivity,fun γ p hp P hP hsmall β ha1 => ?_⟩
  let X := P^finrank ℚ K
  let Z := (P/(p:ℝ))^finrank ℚ K
  let a := auxiliaryRootArcRatio P p γ β
  let F := compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
    (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0
  let G := smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
    (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β)))
  let A := auxiliaryRootMaskedMain rho R P γ p (Nat.ne_of_gt hp) β
  let B := auxiliaryRootScaledMain rho R P γ p β
  have hX : 0≤X := pow_nonneg hP.le _
  have hZ : 0≤Z := pow_nonneg (div_pos hP (Nat.cast_pos.mpr hp)).le _
  have ha0 : 0≤a := auxiliaryRootArcRatio_nonneg P hP p γ β
  have han : 0≤a^N := pow_nonneg ha0 N
  have han1 : a^N≤1 := pow_le_one₀ ha0 ha1
  have herrF : ‖F-A‖≤2*CF*X*a^N :=
    (hf γ p (Nat.ne_of_gt hp) P hP β).trans (by
      change CF*X*a^N*(1+a)≤_
      calc
        _ ≤ CF*X*a^N*2 := mul_le_mul_of_nonneg_left (by linarith only [ha1]) (by positivity)
        _ = _ := by ring)
  have herrG : ‖G-B‖≤2*CG*Z*a^N :=
    (hg γ p hp P hP β).trans (by
      change CG*Z*a^N*(1+a)≤_
      calc
        _ ≤ CG*Z*a^N*2 := mul_le_mul_of_nonneg_left (by linarith only [ha1]) (by positivity)
        _ = _ := by ring)
  have ht' := ht P p hp hsmall (Submodule.Quotient.mk (mixedEmbedding K γ+β))
  have hFD : ‖F‖≤D*X := ht'.1.trans (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) hX)
  have hGD : ‖G‖≤D*Z := ht'.2.trans (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith) hZ)
  have hAD : ‖A‖≤D*X := by
    have htri : ‖A‖≤‖F‖+‖F-A‖ := by
      calc
        ‖A‖ = ‖F-(F-A)‖ := by congr 1; ring
        _ ≤ ‖F‖+‖F-A‖ := norm_sub_le _ _
    apply htri.trans
    calc
      _ ≤ CT*X+2*CF*X*a^N := add_le_add ht'.1 herrF
      _ ≤ CT*X+2*CF*X := add_le_add_left
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left han1 (by positivity : 0≤2*CF*X)) _
      _ ≤ D*X := by dsimp only [D]; nlinarith only [mul_nonneg hCG.le hX]
  have hBD : ‖B‖≤D*Z := by
    have htri : ‖B‖≤‖G‖+‖G-B‖ := by
      calc
        ‖B‖ = ‖G-(G-B)‖ := by congr 1; ring
        _ ≤ ‖G‖+‖G-B‖ := norm_sub_le _ _
    apply htri.trans
    calc
      _ ≤ CT*Z+2*CG*Z*a^N := add_le_add ht'.2 herrG
      _ ≤ CT*Z+2*CG*Z := add_le_add_left
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left han1 (by positivity : 0≤2*CG*Z)) _
      _ ≤ D*Z := by dsimp only [D]; nlinarith only [mul_nonneg hCF.le hZ]
  exact (norm_four_by_four_sub_le F G A B (mul_nonneg hD.le hX) (mul_nonneg hD.le hZ)
    (by positivity) (by positivity) hFD hAD hGD hBD herrF herrG).trans_eq (by
      change _=8*D^7*(CF+CG)*X^4*Z^4*a^N
      ring)

#print axioms norm_fourth_sub_fourth_le
#print axioms norm_four_by_four_sub_le
#print axioms auxiliary_root_eightfold_main_error
end WaringSiegel.WSL4
