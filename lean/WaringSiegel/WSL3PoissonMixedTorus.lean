import WaringSiegel.WSL3PoissonMixedCubicWeyl
import WaringSiegel.WSL3PoissonMixedQuadraticBounds
import WaringSiegel.WSL2TraceCubicDiagonal

/-! # Actual compact smooth sums and quadratic averages on the trace torus -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def compactTraceWeylSum (k : ℕ) (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) : ArchimedeanTraceTorus K → ℂ :=
  traceWeylSum k (fun x : compactIntegerSupport w hc P hP => (x:𝓞 K))
    (fun x => w (P⁻¹ • mixedEmbedding K ((x:𝓞 K):K)))

theorem compactTraceWeylSum_continuous (k : ℕ) (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) : Continuous (compactTraceWeylSum k w hc P hP) :=
  traceWeylSum_continuous _ _ _

theorem compactTraceWeylSum_mk (k : ℕ) (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) :
    compactTraceWeylSum k w hc P hP (Submodule.Quotient.mk θ) =
      ∑' x : 𝓞 K, w (P⁻¹ • mixedEmbedding K (x:K)) *
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k) := by
  unfold compactTraceWeylSum
  rw [traceWeylSum_mk]
  have hphase (x : 𝓞 K) : Complex.exp (2*Real.pi*Complex.I*
      (archimedeanTrace (mixedEmbedding K ((x^k:𝓞 K):K)*θ):ℂ)) =
      archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k) := by
    simp only [map_pow,archimedeanTraceCharacter,mul_comm ((mixedEmbedding K (x:K))^k) θ]
  simp_rw [hphase]
  rw [Finset.sum_coe_sort (compactIntegerSupport w hc P hP)
    (fun x : 𝓞 K => w (P⁻¹ • mixedEmbedding K (x:K)) *
      archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k))]
  symm
  apply tsum_eq_sum
  intro x hx
  have hz : w (P⁻¹ • mixedEmbedding K (x:K)) = 0 := by
    by_contra hn
    exact hx ((mem_compactIntegerSupport w hc P hP x).mpr hn)
  rw [hz,zero_mul]

theorem compactTraceWeylSum_three_mk (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) :
    compactTraceWeylSum 3 w hc P hP (Submodule.Quotient.mk θ) = compactCubicSum w P θ 0 0 := by
  rw [compactTraceWeylSum_mk]
  simp only [compactCubicSum,traceCubicNodePhase,zero_mul,add_zero,traceCharacter_one_mul]

theorem compactTraceWeylSum_two_mk (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (θ : mixedSpace K) :
    compactTraceWeylSum 2 w hc P hP (Submodule.Quotient.mk θ) = compactQuadraticSum w P θ 0 := by
  rw [compactTraceWeylSum_mk]
  simp only [compactQuadraticSum,traceQuadraticNodePhase,zero_mul,add_zero,traceCharacter_one_mul]

def compactTraceQuadraticAverage (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (U : Finset (𝓞 K)) (q : ArchimedeanTraceTorus K) : ℝ :=
  ∑ h ∈ U, ‖compactTraceWeylSum 2 w hc P hP (traceTorusMul (3*h) q)‖^2

theorem compactTraceQuadraticAverage_nonneg (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (U : Finset (𝓞 K)) (q : ArchimedeanTraceTorus K) :
    0 ≤ compactTraceQuadraticAverage w hc P hP U q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem compactTraceQuadraticAverage_continuous (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (U : Finset (𝓞 K)) :
    Continuous (compactTraceQuadraticAverage w hc P hP U) := by
  apply continuous_finset_sum
  intro h hh
  exact ((compactTraceWeylSum_continuous 2 w hc P hP).comp (traceTorusMul_continuous (3*h))).norm.pow 2

theorem compactTraceQuadraticAverage_mk (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (U : Finset (𝓞 K)) (θ : mixedSpace K) :
    compactTraceQuadraticAverage w hc P hP U (Submodule.Quotient.mk θ) =
      ∑ h ∈ U, ‖compactQuadraticSum w P (3*θ*mixedEmbedding K (h:K)) 0‖^2 := by
  unfold compactTraceQuadraticAverage
  simp_rw [traceTorusMul_mk,compactTraceWeylSum_two_mk]
  apply Finset.sum_congr rfl
  intro h hh
  congr 3
  simp only [map_mul,map_ofNat]
  ring

theorem six_smul_mixed (θ : mixedSpace K) : (6:ℝ) • θ = (6:mixedSpace K)*θ := by
  simpa only [Nat.cast_ofNat,nsmul_eq_mul] using Nat.cast_smul_eq_nsmul ℝ 6 θ

/-- The cubic Weyl saving on the literal quotient, including the multiplier
in the major-arc conductor cutoff. -/
theorem compactTraceCubicSum_minor_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P), ∀ q : ArchimedeanTraceTorus K,
      q ∉ traceMajorArcUnion (P^2*(4*P)) ((6:ℝ)^finrank ℚ K*P^finrank ℚ K) →
      ‖compactTraceWeylSum 3 w hc P (by linarith) q‖^4 ≤ C*(P^finrank ℚ K)^3*P^ε := by
  obtain ⟨C,hC,hb⟩ := compactCubicSum_minor_bound hw hc hsupport hε
  refine ⟨C,hC,fun P hP q hminor => ?_⟩
  obtain ⟨θ,rfl⟩ := Quotient.exists_rep q
  change ‖compactTraceWeylSum 3 w hc P _ (Submodule.Quotient.mk θ)‖^4 ≤ _
  rw [compactTraceWeylSum_three_mk]
  apply hb P hP θ 0 0
  have h := traceMajorArcUnion_smul_nat_preimage (P^2*(4*P)) (P^finrank ℚ K)
    (by positivity) θ 6 (by norm_num) hminor
  simpa only [Nat.cast_ofNat,six_smul_mixed,traceConductor] using h

/-- The quadratic minor average on the literal trace torus. -/
theorem compactTraceQuadraticAverage_minor_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ) (hP : 1 ≤ P), 1 ≤ H → H ≤ P → P ≤ H^2 →
      ∀ q : ArchimedeanTraceTorus K,
      q ∉ traceMajorArcUnion (P^2*(2*H)) ((6:ℝ)^finrank ℚ K*P^finrank ℚ K) →
      ∀ U : Finset (𝓞 K), (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      compactTraceQuadraticAverage w hc P (by linarith) U q ≤ C*P^finrank ℚ K*H^finrank ℚ K*P^ε := by
  obtain ⟨C,hC,hb⟩ := compactQuadraticAverage_minor_bound hw hc hsupport hε
  refine ⟨C,hC,fun P H hP hH hHP hPH q hminor U hU0 hU => ?_⟩
  obtain ⟨θ,rfl⟩ := Quotient.exists_rep q
  change compactTraceQuadraticAverage w hc P _ U (Submodule.Quotient.mk θ) ≤ _
  rw [compactTraceQuadraticAverage_mk]
  apply hb P H hP hH hHP hPH θ _ (fun _ => 0) U hU0 hU
  have h := traceMajorArcUnion_smul_nat_preimage (P^2*(2*H)) (P^finrank ℚ K)
    (by positivity) θ 6 (by norm_num) hminor
  simpa only [Nat.cast_ofNat,six_smul_mixed,traceConductor] using h

/-- The actual cubic fourth moment, with one constant before the scale. -/
theorem compactTraceCubicSum_fourth_moment {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q, ‖compactTraceWeylSum 3 w hc P (by linarith) q‖^4 ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hb⟩ := numberField_fourth_moment_bound (K:=K) 3 (by norm_num) hε
  obtain ⟨W,hW⟩ := hw.continuous.bounded_above_of_compact_support hc
  let V := |W|+1
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨C*V^4,by positivity,fun P hP => ?_⟩
  have hP0 : 0 < P := by linarith
  let S := compactIntegerSupport w hc P hP0.ne'
  have hweights : ∀ x : S, ‖w (P⁻¹ • mixedEmbedding K ((x:𝓞 K):K))‖ ≤ V :=
    fun x => (hW _).trans ((le_abs_self W).trans (by dsimp [V]; linarith))
  have hbox : ∀ x : S, ∀ v : InfinitePlace K, v ((x:𝓞 K):K) ≤ P := by
    intro x v
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans
      (compactIntegerSupport_norm_bound hc hsupport P hP0 x.property)
  change (∫ q, ‖traceWeylSum 3 (fun x:S => (x:𝓞 K))
      (fun x => w (P⁻¹ • mixedEmbedding K ((x:𝓞 K):K))) q‖^4 ∂traceHaar) ≤ _
  rw [traceWeylSum_integral_norm_pow]
  exact (hb P hP (fun x:S => (x:𝓞 K)) Subtype.val_injective hbox
    (fun x => w (P⁻¹ • mixedEmbedding K ((x:𝓞 K):K))) V hV.le hweights).trans_eq (by ring)

/-- Any nonzero algebraic-integer multiplier preserves this fourth moment. -/
theorem compactTraceCubicSum_mul_fourth_moment {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P), ∀ a : 𝓞 K, a ≠ 0 →
      (∫ q, ‖compactTraceWeylSum 3 w hc P (by linarith) (traceTorusMul a q)‖^4 ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hb⟩ := compactTraceCubicSum_fourth_moment hw hc hsupport hε
  refine ⟨C,hC,fun P hP a ha => ?_⟩
  rw [compactTraceWeylSum,traceWeylSum_mul_integral_norm_pow a ha]
  exact hb P hP

end WaringSiegel.WSL3Poisson
