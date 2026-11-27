import WaringSiegel.WSL4ArchFourthArc
import WaringSiegel.WSL3PoissonMajorFourthCenters

/-! # Actual major-fourth integration with exact conductor counting

The analytic bound applies to the actual product bump equal one near zero. The two inputs
in the final numerical theorem are explicit: a bound for the literal finite
twisted complete sums and a truncated fourth-power ideal-weight sum.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nearZeroTraceCubicSum_major_fourth_conductor_bound
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Ideal (𝓞 K) → ℝ), (∀ I, 0 ≤ κ I) →
      (∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ (traceConductor γ)) →
      ∀ (P : ℝ) (hP : 0 < P),
      (∫ q in traceMajorArcUnion (K := K) (P^3) (L*P^finrank ℚ K),
        ‖nearZeroTraceCubicSum (K := K) P hP.ne' q‖^4 ∂traceHaar) ≤
        C*P^finrank ℚ K *
          ∑ I ∈ cubicConductorCutoff ⌊L*P^finrank ℚ K⌋₊,
            (Ideal.absNorm I.1 : ℝ)*κ I.1^4 := by
  obtain ⟨C,hC,hb⟩ := nearZeroTraceCubicSum_single_arc_fourth (K := K) L hL
  refine ⟨C,hC,?_⟩
  intro κ hκ hfinite P hP
  let W := P^finrank ℚ K
  let N := ⌊L*W⌋₊
  letI := Fintype.ofFinite (traceRationalCenters K N)
  let f : ArchimedeanTraceTorus K → ℝ := fun q => ‖nearZeroTraceCubicSum (K := K) P hP.ne' q‖^4
  have hfc : Continuous f := (nearZeroTraceCubicSum_continuous P hP.ne').norm.pow 4
  have hfn : ∀ q, 0 ≤ f q := fun _ => pow_nonneg (norm_nonneg _) _
  have hu := traceHaar_integral_finite_union_le
    (fun q : traceRationalCenters K N => traceMajorArc (P^3) (L*W) (traceCenterRepresentative q))
    (fun q => traceMajorArc_measurableSet _ _ (pow_pos hP 3) _) f hfc hfn
  calc
    _ ≤ ∑ q : traceRationalCenters K N,
        ∫ θ in traceMajorArc (P^3) (L*W) (traceCenterRepresentative q), f θ ∂traceHaar := by
      simpa only [traceMajorArcUnion_eq_finite_union,f,W,N] using hu
    _ ≤ ∑ q : traceRationalCenters K N, C*κ (traceConductor (traceCenterRepresentative q))^4*W :=
      Finset.sum_le_sum (fun q _ => hb _ _ (hκ _) (hfinite _) P hP)
    _ = C*W * ∑ q : traceRationalCenters K N, κ (traceConductor (traceCenterRepresentative q))^4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ C*W * ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1 : ℝ)*κ I.1^4 :=
      mul_le_mul_of_nonneg_left (traceRationalCenters_weight_sum_le N κ) (by dsimp [W]; positivity)

/-- Numerical major-fourth saving for the actual near-zero product bump.
The explicit arithmetic truncated-mass estimate is the only premise besides
the literal finite twisted complete-sum bound. -/
theorem nearZeroTraceCubicSum_major_fourth_of_weight_bound
    (L : ℝ) (hL : 1 ≤ L)
    (ε : ℝ) (hε : 0 < ε) (κ : Ideal (𝓞 K) → ℝ) (hκ : ∀ I, 0 ≤ κ I)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*κ (traceConductor γ))
    (A : ℝ) (hA : 0 < A)
    (hweight : ∀ N : ℕ, 1 ≤ N →
      (∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1 : ℝ)*κ I.1^4) ≤ A*(N:ℝ)^ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in traceMajorArcUnion (K := K) (P^3) (L*P^finrank ℚ K),
        ‖nearZeroTraceCubicSum (K := K) P (by linarith) q‖^4 ∂traceHaar) ≤
          C*(P^finrank ℚ K : ℝ)^(1+ε) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨C,hC,hb⟩ := nearZeroTraceCubicSum_major_fourth_conductor_bound (K := K) L hL0.le
  refine ⟨C*A*L^ε,by positivity,?_⟩
  intro P hP
  have hP0 : 0 < P := by linarith
  let W := P^finrank ℚ K
  let N := ⌊L*W⌋₊
  have hW1 : 1 ≤ W := one_le_pow₀ hP
  have hW : 0 < W := lt_of_lt_of_le zero_lt_one hW1
  have hLW : 1 ≤ L*W := one_le_mul_of_one_le_of_one_le hL hW1
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hLW)
  have hpow : (N:ℝ)^ε ≤ (L*W)^ε :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) hε.le
  calc
    _ ≤ C*W * ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1 : ℝ)*κ I.1^4 :=
      hb κ hκ hfinite P hP0
    _ ≤ C*W*(A*(N:ℝ)^ε) := mul_le_mul_of_nonneg_left (hweight N hN) (by positivity)
    _ ≤ C*W*(A*(L*W)^ε) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpow hA.le) (by positivity)
    _ = (C*A*L^ε)*W^(1+ε) := by
      rw [Real.mul_rpow hL0.le hW.le,Real.rpow_add hW,Real.rpow_one]
      ring

end WaringSiegel.WSL4
#print axioms WaringSiegel.WSL4.nearZeroTraceCubicSum_major_fourth_conductor_bound
#print axioms WaringSiegel.WSL4.nearZeroTraceCubicSum_major_fourth_of_weight_bound
