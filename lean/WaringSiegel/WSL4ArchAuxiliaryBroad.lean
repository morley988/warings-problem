import WaringSiegel.WSL4ArchRootScaled
import WaringSiegel.WSL4WeilMaskedComplete
import WaringSiegel.WSL4WeilKappaPrimeCube

/-! # Prime-uniform broad bounds for the actual four-by-four cubic product

Both sources have the same product weight at scale P³. The full growing
packing factor is retained; it is not absorbed into a prime-dependent
constant. All finite exponential sum estimates are discharged.
-/
noncomputable section
set_option maxHeartbeats 1900000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
  WaringSiegel.WSL4Weil
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliary_root_sources_broad_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : p.Prime), 6<p →
      ∀ (P : ℝ) (hP : 0<P) (β : mixedSpace K),
    let V := C*cubicKappa cubicTwistExceptionalConstant ⟨traceConductor γ,traceConductor_ne_zero γ⟩*
      P^finrank ℚ K*(productArcWeight (P^3) β)^(-(1/2):ℝ)*
        (1+(p:ℝ)^finrank ℚ K*((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) β/P^finrank ℚ K)
    ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
      (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0‖≤V ∧
    ‖smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp.pos)).ne'
      (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β)))‖≤V := by
  obtain ⟨CF,hCF,hf⟩ := smoothRootCubic_masked_packing_bound (K:=K) rho R hrho hR
  obtain ⟨CG,hCG,hg⟩ := smoothRootCubic_scaled_packing_bound (K:=K) rho R hrho hR
  refine ⟨CF*(2:ℝ)^finrank ℚ K+CG,by positivity,fun γ p hp hp6 P hP β => ?_⟩
  let κ := cubicKappa cubicTwistExceptionalConstant ⟨traceConductor γ,traceConductor_ne_zero γ⟩
  let X := P^finrank ℚ K
  let Y := (p:ℝ)^finrank ℚ K
  let Z := (P/(p:ℝ))^finrank ℚ K
  let Q : ℝ := (traceConductor γ).absNorm
  let Q' : ℝ := (traceConductor ((p:K)^3*γ)).absNorm
  let A := productArcWeight (P^3) β
  have hκ : 0≤κ := cubicKappa_nonneg _ cubicTwistExceptionalConstant_nonneg _
  have hX : 0<X := pow_pos hP _
  have hY : 0<Y := pow_pos (Nat.cast_pos.mpr hp.pos) _
  have hZ : 0<Z := pow_pos (div_pos hP (Nat.cast_pos.mpr hp.pos)) _
  have hQ : 0≤Q := Nat.cast_nonneg _
  have hA : 0<A := productArcWeight_pos _ _
  have hZY : Y*Z=X := by
    dsimp only [Y,Z,X]
    rw [div_pow]
    field_simp [show (p:ℝ)≠0 from Nat.cast_ne_zero.mpr hp.ne_zero]
  have hQ' : Q'≤Q := by
    have hh := traceConductor_integral_mul_norm_le ((p:𝓞 K)^3) γ
    have hh' : (traceConductor ((p:K)^3*γ)).absNorm≤(traceConductor γ).absNorm := by
      simpa only [RingOfIntegers.coe_eq_algebraMap,map_pow,map_natCast] using hh
    dsimp only [Q',Q]
    exact_mod_cast hh'
  have hpack : 1+Q'*A/Z≤1+Y*Q*A/X := by
    apply add_le_add_left
    apply (div_le_div_iff₀ hZ hX).mpr
    calc
      Q'*A*X = Q'*A*(Y*Z) := by rw [hZY]
      _ ≤ Y*Q*A*Z := by nlinarith only [mul_nonneg (sub_nonneg.mpr hQ') (mul_nonneg hA.le (mul_nonneg hY.le hZ.le))]
  have hκp := cubicKappa_prime_cube_mul_bound cubicTwistExceptionalConstant
    cubicTwistExceptionalConstant_nonneg p hp hp6 γ
  have hf' := hf γ p hp.ne_zero ((2:ℝ)^finrank ℚ K*κ) (by positivity)
    (fun ξ => auxiliaryMaskedTwistedComplete_kappa_bound (fieldCenterCubicCharacter γ) p hp
      (Nat.cast_ne_zero.mpr hp.ne_zero) ξ) P hP β
  have hg' := hg γ p hp.pos (Y*κ) (mul_nonneg hY.le hκ) (by
    intro ξ
    exact (fieldCenterCompleteSum_cubic_kappa_bound ((p:K)^3*γ) ξ).trans
      (mul_le_mul_of_nonneg_left hκp (Nat.cast_nonneg _))) P hP β
  have htail : 0≤A^(-(1/2):ℝ) := Real.rpow_nonneg hA.le _
  have hpack0 : 0≤1+Y*Q*A/X := by positivity
  constructor
  · apply hf'.trans
    change CF*((2:ℝ)^finrank ℚ K*κ)*X*A^(-(1/2):ℝ)*(1+Y*Q*A/X)≤_
    have hh := mul_le_mul_of_nonneg_right
      (show CF*(2:ℝ)^finrank ℚ K≤CF*(2:ℝ)^finrank ℚ K+CG by linarith)
      (mul_nonneg (mul_nonneg (mul_nonneg hκ hX.le) htail) hpack0)
    nlinarith only [hh]
  · apply hg'.trans
    change CG*(Y*κ)*Z*A^(-(1/2):ℝ)*(1+Q'*A/Z)≤_
    calc
      _ ≤ CG*(Y*κ)*Z*A^(-(1/2):ℝ)*(1+Y*Q*A/X) :=
        mul_le_mul_of_nonneg_left hpack (by positivity)
      _ = CG*κ*X*A^(-(1/2):ℝ)*(1+Y*Q*A/X) := by rw [← hZY]; ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right
          (show CG≤CF*(2:ℝ)^finrank ℚ K+CG from le_add_of_nonneg_left (by positivity))
          (mul_nonneg (mul_nonneg (mul_nonneg hκ hX.le) htail) hpack0)
        nlinarith only [hh]

theorem auxiliary_root_four_by_four_broad_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : p.Prime), 6<p →
      ∀ (P : ℝ) (hP : 0<P) (β : mixedSpace K),
    ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
      (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0‖^4 *
    ‖smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp.pos)).ne'
      (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β)))‖^4 ≤
    C*(P^finrank ℚ K)^8*
      (cubicKappa cubicTwistExceptionalConstant ⟨traceConductor γ,traceConductor_ne_zero γ⟩)^8*
      (productArcWeight (P^3) β)^(-4:ℝ)*
      (1+(p:ℝ)^finrank ℚ K*((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) β/P^finrank ℚ K)^8 := by
  obtain ⟨C,hC,hb⟩ := auxiliary_root_sources_broad_bound (K:=K) rho R hrho hR
  refine ⟨C^8,pow_pos hC _,fun γ p hp hp6 P hP β => ?_⟩
  obtain ⟨hf,hg⟩ := hb γ p hp hp6 P hP β
  have hh := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hf 4)
    (pow_le_pow_left₀ (norm_nonneg _) hg 4) (by positivity) (by positivity)
  apply hh.trans_eq
  have hA := productArcWeight_pos (P^3) β
  have he : ((productArcWeight (P^3) β)^(-(1/2):ℝ))^8=
      (productArcWeight (P^3) β)^(-4:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
    norm_num
  simp only [mul_pow]
  calc
    _ = C^8*(P^finrank ℚ K)^8*
        (cubicKappa cubicTwistExceptionalConstant ⟨traceConductor γ,traceConductor_ne_zero γ⟩)^8*
        ((productArcWeight (P^3) β)^(-(1/2):ℝ))^8*
        (1+(p:ℝ)^finrank ℚ K*((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) β/P^finrank ℚ K)^8 := by ring
    _ = _ := by rw [he]

#print axioms auxiliary_root_sources_broad_bound
#print axioms auxiliary_root_four_by_four_broad_bound
end WaringSiegel.WSL4
