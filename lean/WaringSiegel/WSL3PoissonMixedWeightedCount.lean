import WaringSiegel.WSL3PoissonMixedFourierProducts

/-! # Exact weighted transformed mixed count on the actual trace torus -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField WaringSiegel.WSL2
open scoped NumberField BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

def mixedWeightedTraceAggregate (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (u : α → ℂ) (w : β → ℂ) (g : γ → ℂ) (v : δ → ℂ)
    (q : ArchimedeanTraceTorus K) : ℂ :=
  (∑ a : α, u a*traceWeylSum 2 z w (traceTorusMul (3*h a) q)*
    traceWeylSum 6 m g (traceTorusMul (h a^3) q)) *
      ((‖traceWeylSum 3 y v (traceTorusMul 4 q)‖^4:ℝ):ℂ)

def mixedWeightedPhase (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (p : α×((β×γ)×((δ×δ)×(δ×δ)))) : 𝓞 K :=
  (3*h p.1*z p.2.1.1^2+h p.1^3*m p.2.1.2^6)+
    4*((y p.2.2.1.1^3-y p.2.2.1.2^3)+(y p.2.2.2.1^3-y p.2.2.2.2^3))

def mixedWeightedCoefficient (u : α → ℂ) (w : β → ℂ) (g : γ → ℂ) (v : δ → ℂ)
    (p : α×((β×γ)×((δ×δ)×(δ×δ)))) : ℂ :=
  u p.1*((w p.2.1.1*g p.2.1.2)*
    ((v p.2.2.1.1*conj (v p.2.2.1.2))*(v p.2.2.2.1*conj (v p.2.2.2.2))))

/-- The frequency-zero condition is the literal transformed cubic equation. -/
theorem mixedWeightedPhase_eq_zero_iff (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (p : α×((β×γ)×((δ×δ)×(δ×δ)))) :
    mixedWeightedPhase h z m y p=0 ↔
      h p.1*(3*z p.2.1.1^2+h p.1^2*m p.2.1.2^6)=
        4*(y p.2.2.1.2^3+y p.2.2.2.2^3-y p.2.2.1.1^3-y p.2.2.2.1^3) := by
  have he : mixedWeightedPhase h z m y p =
      h p.1*(3*z p.2.1.1^2+h p.1^2*m p.2.1.2^6)-
        4*(y p.2.2.1.2^3+y p.2.2.2.2^3-y p.2.2.1.1^3-y p.2.2.2.1^3) := by
    unfold mixedWeightedPhase
    ring
  rw [he,sub_eq_zero]

theorem mixedWeightedTraceAggregate_expansion (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (u : α → ℂ) (w : β → ℂ) (g : γ → ℂ) (v : δ → ℂ)
    (q : ArchimedeanTraceTorus K) :
    mixedWeightedTraceAggregate h z m y u w g v q =
      traceFrequencySum (mixedWeightedPhase h z m y) (mixedWeightedCoefficient u w g v) q := by
  have hf (a : α) :
      (u a*traceWeylSum 2 z w (traceTorusMul (3*h a) q)*
        traceWeylSum 6 m g (traceTorusMul (h a^3) q)) *
          ((‖traceWeylSum 3 y v (traceTorusMul 4 q)‖^4:ℝ):ℂ) =
      traceFrequencySum (fun p => mixedWeightedPhase h z m y (a,p))
        (fun p => mixedWeightedCoefficient u w g v (a,p)) q := by
    calc
      _ = u a*((traceWeylSum 2 z w (traceTorusMul (3*h a) q)*
          traceWeylSum 6 m g (traceTorusMul (h a^3) q))*
            ((‖traceWeylSum 3 y v (traceTorusMul 4 q)‖^4:ℝ):ℂ)) := by ring
      _ = _ := by
        rw [traceWeylSum_mul_eq_traceFrequencySum,traceWeylSum_mul_eq_traceFrequencySum,
          traceWeylSum_norm_fourth_expansion,traceFrequencySum_mul_arg,
          traceFrequencySum_mul,traceFrequencySum_mul,traceFrequencySum_const_mul]
        rfl
  unfold mixedWeightedTraceAggregate
  rw [Finset.sum_mul]
  simp_rw [hf]
  exact traceFrequencySum_sum _ _ _

/-- Exact integral/count identity. No pointwise positivity of the complex
aggregate is used. -/
theorem mixedWeightedTraceAggregate_integral (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (u : α → ℂ) (w : β → ℂ) (g : γ → ℂ) (v : δ → ℂ) :
    (∫ q, mixedWeightedTraceAggregate h z m y u w g v q ∂traceHaar) =
      ∑ p, if mixedWeightedPhase h z m y p=0 then mixedWeightedCoefficient u w g v p else 0 := by
  simp_rw [mixedWeightedTraceAggregate_expansion]
  exact traceFrequencySum_integral _ _

def mixedWeightedRealCount (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (u : α → ℝ) (w : β → ℝ) (g : γ → ℝ) (v : δ → ℝ) : ℝ :=
  ∑ p : α×((β×γ)×((δ×δ)×(δ×δ))), if mixedWeightedPhase h z m y p=0 then
    u p.1*((w p.2.1.1*g p.2.1.2)*
      ((v p.2.2.1.1*v p.2.2.1.2)*(v p.2.2.2.1*v p.2.2.2.2))) else 0

theorem mixedWeightedRealCount_nonneg (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (u : α → ℝ) (w : β → ℝ) (g : γ → ℝ) (v : δ → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hw : ∀ a, 0 ≤ w a) (hg : ∀ a, 0 ≤ g a) (hv : ∀ a, 0 ≤ v a) :
    0 ≤ mixedWeightedRealCount h z m y u w g v := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact mul_nonneg (hu _) (mul_nonneg (mul_nonneg (hw _) (hg _))
      (mul_nonneg (mul_nonneg (hv _) (hv _)) (mul_nonneg (hv _) (hv _))))
  · exact le_rfl

theorem mixedWeightedTraceAggregate_integral_real (h : α → 𝓞 K) (z : β → 𝓞 K)
    (m : γ → 𝓞 K) (y : δ → 𝓞 K) (u : α → ℝ) (w : β → ℝ) (g : γ → ℝ) (v : δ → ℝ) :
    (∫ q, mixedWeightedTraceAggregate h z m y
      (fun a => (u a:ℂ)) (fun a => (w a:ℂ)) (fun a => (g a:ℂ)) (fun a => (v a:ℂ)) q ∂traceHaar) =
      (mixedWeightedRealCount h z m y u w g v:ℂ) := by
  rw [mixedWeightedTraceAggregate_integral]
  simp only [mixedWeightedRealCount,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · simp only [mixedWeightedCoefficient,Complex.conj_ofReal,Complex.ofReal_mul]
  · exact (Complex.ofReal_zero).symm

end WaringSiegel.WSL3Poisson
