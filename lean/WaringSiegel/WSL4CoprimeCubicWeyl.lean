import WaringSiegel.WSL4CoprimeWeylTransfer

/-! # The literal coprime cubic Weyl bound, uniform in the prime and linear twist -/
noncomputable section
set_option maxHeartbeats 900000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical ContDiff
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusCharacter_mk_archimedean (x : 𝓞 K) (θ : mixedSpace K) :
    traceTorusCharacter x (Submodule.Quotient.mk θ) =
      archimedeanTraceCharacter θ (mixedEmbedding K (x : K)) := by
  simp only [traceTorusCharacter_mk,archimedeanTraceCharacter,
    mul_comm (mixedEmbedding K (x : K)) θ]

theorem finiteLinearTraceCubic_mk (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (θ β : mixedSpace K) :
    finiteLinearTraceSum (compactIntegerSupport w hc P hP)
      (fun x => w (P⁻¹ • mixedEmbedding K (x : K)) *
        traceTorusCharacter (x^3) (Submodule.Quotient.mk θ))
      (Submodule.Quotient.mk β) = compactCubicSum w P θ 0 β := by
  have hphase (x : 𝓞 K) :
      traceTorusCharacter (x^3) (Submodule.Quotient.mk θ) *
        traceTorusCharacter x (Submodule.Quotient.mk β) = traceCubicNodePhase θ 0 β x := by
    simp only [traceTorusCharacter_mk_archimedean,map_pow,traceCubicNodePhase,
      zero_mul,add_zero,archimedeanTraceCharacter_add,traceCharacter_one_mul]
  unfold finiteLinearTraceSum compactCubicSum
  simp_rw [mul_assoc,hphase]
  symm
  apply tsum_eq_sum
  intro x hx
  have hz : w (P⁻¹ • mixedEmbedding K (x : K)) = 0 := by
    by_contra hn
    exact hx ((mem_compactIntegerSupport w hc P hP x).mpr hn)
  rw [hz,zero_mul]

def compactCoprimeTraceCubicSum (w : mixedSpace K → ℂ) (P : ℝ) (p : ℕ)
    (q r : ArchimedeanTraceTorus K) : ℂ :=
  ∑' x : 𝓞 K, if IsUnit (Ideal.Quotient.mk
      (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) x) then
    w (P⁻¹ • mixedEmbedding K (x : K)) * traceTorusCharacter (x^3) q *
      traceTorusCharacter x r else 0

theorem compactCoprimeTraceCubicSum_eq_finite
    (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (p : ℕ) (q r : ArchimedeanTraceTorus K) :
    compactCoprimeTraceCubicSum w P p q r =
      finiteLinearTraceSum ((compactIntegerSupport w hc P hP).filter
        (fun x => IsUnit (Ideal.Quotient.mk
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) x)))
        (fun x => w (P⁻¹ • mixedEmbedding K (x : K)) * traceTorusCharacter (x^3) q) r := by
  unfold compactCoprimeTraceCubicSum finiteLinearTraceSum
  rw [Finset.sum_filter]
  apply tsum_eq_sum
  intro x hx
  have hz : w (P⁻¹ • mixedEmbedding K (x : K)) = 0 := by
    by_contra hn
    exact hx ((mem_compactIntegerSupport w hc P hP x).mpr hn)
  simp only [hz,zero_mul,ite_self]

theorem compactCoprimeTraceCubicSum_minor_fourth_bound {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P), ∀ p : ℕ, p.Prime →
      ∀ q r : ArchimedeanTraceTorus K,
      q ∉ traceMajorArcUnion (P^2*(4*P)) ((6 : ℝ)^finrank ℚ K*P^finrank ℚ K) →
      ‖compactCoprimeTraceCubicSum w P p q r‖^4 ≤ C*(P^finrank ℚ K)^3*P^ε := by
  obtain ⟨C,hC,hbound⟩ := compactCubicSum_minor_bound hw hc hsupport hε
  refine ⟨((2 : ℝ)^finrank ℚ K)^4*C,by positivity,fun P hP p hp q r hminor => ?_⟩
  have hP0 : 0 < P := by linarith
  let S := compactIntegerSupport w hc P hP0.ne'
  let f : 𝓞 K → ℂ := fun x => w (P⁻¹ • mixedEmbedding K (x : K)) * traceTorusCharacter (x^3) q
  have hB (t : ArchimedeanTraceTorus K) :
      ‖finiteLinearTraceSum S f t‖^4 ≤ C*(P^finrank ℚ K)^3*P^ε := by
    obtain ⟨θ,rfl⟩ := Quotient.exists_rep q
    obtain ⟨β,rfl⟩ := Quotient.exists_rep t
    change ‖finiteLinearTraceSum (compactIntegerSupport w hc P hP0.ne')
      (fun x => w (P⁻¹ • mixedEmbedding K (x : K)) * traceTorusCharacter (x^3)
        (Submodule.Quotient.mk θ)) (Submodule.Quotient.mk β)‖^4 ≤ _
    rw [finiteLinearTraceCubic_mk]
    apply hbound P hP θ 0 β
    have h := traceMajorArcUnion_smul_nat_preimage (P^2*(4*P)) (P^finrank ℚ K)
      (by positivity) θ 6 (by norm_num) hminor
    simpa only [Nat.cast_ofNat,six_smul_mixed,traceConductor] using h
  rw [compactCoprimeTraceCubicSum_eq_finite w hc P hP0.ne']
  exact (finiteLinearTraceSum_coprime_prime_fourth_bound S f
    (C*(P^finrank ℚ K)^3*P^ε) (by positivity) hB p hp r).trans_eq (by ring)

#print axioms finiteLinearTraceCubic_mk
#print axioms compactCoprimeTraceCubicSum_eq_finite
#print axioms compactCoprimeTraceCubicSum_minor_fourth_bound
end WaringSiegel.WSL4Local
