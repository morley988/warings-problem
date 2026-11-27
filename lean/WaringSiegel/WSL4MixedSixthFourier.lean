import WaringSiegel.WSL3PoissonMixedFourierProducts
import WaringSiegel.WSL2TraceCubicMixed

/-! # Exact second-times-fourth trace moments as nonnegative weighted counts -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField
open scoped NumberField BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {α β : Type*} [Fintype α] [Fintype β]

def mixedSecondFourthPhase (a : 𝓞 K) (x : α → 𝓞 K) (y : β → 𝓞 K)
    (t : (α × α) × ((β × β) × (β × β))) : 𝓞 K :=
  (x t.1.1^3-x t.1.2^3)+a*((y t.2.1.1^3-y t.2.1.2^3)+(y t.2.2.1^3-y t.2.2.2^3))

def mixedSecondFourthCoefficient (w : α → ℝ) (v : β → ℝ)
    (t : (α × α) × ((β × β) × (β × β))) : ℝ :=
  (w t.1.1*w t.1.2)*((v t.2.1.1*v t.2.1.2)*(v t.2.2.1*v t.2.2.2))

theorem trace_second_fourth_integral (a : 𝓞 K) (x : α → 𝓞 K) (y : β → 𝓞 K)
    (w : α → ℝ) (v : β → ℝ) :
    (∫ q, ‖traceWeylSum 3 x (fun i => (w i : ℂ)) q‖^2 *
      ‖traceWeylSum 3 y (fun i => (v i : ℂ)) (traceTorusMul a q)‖^4 ∂traceHaar) =
      ∑ t, if mixedSecondFourthPhase a x y t = 0 then mixedSecondFourthCoefficient w v t else 0 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hsq (q : ArchimedeanTraceTorus K) :
      ((‖traceWeylSum 3 x (fun i => (w i : ℂ)) q‖^2 : ℝ) : ℂ) =
        traceFrequencySum (fun t : α × α => x t.1^3-x t.2^3)
          (fun t => (w t.1 : ℂ)*(w t.2 : ℂ)) q := by
    rw [Complex.ofReal_pow,← Complex.mul_conj',traceWeylSum_mul_conj_expansion]
    simp only [Complex.conj_ofReal,traceFrequencySum]
  simp_rw [Complex.ofReal_mul,hsq,traceWeylSum_norm_fourth_expansion,
    traceFrequencySum_mul_arg,traceFrequencySum_mul]
  rw [traceFrequencySum_integral,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [mixedSecondFourthPhase,mixedSecondFourthCoefficient,
    Complex.conj_ofReal,Complex.ofReal_mul]
  split_ifs <;> simp

def mixedResidueCongruentCount (a : 𝓞 K) (x : α → 𝓞 K) (y : β → 𝓞 K) : ℕ :=
  Fintype.card {t : (α × α) × ((β × β) × (β × β)) //
    Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.1) =
      Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.2) ∧
    mixedSecondFourthPhase a x y t = 0}

theorem unit_pair_indicators_sum_le {Q : Type*} [CommRing Q] [Fintype Q] (x y : Q) :
    (∑ r : Qˣ, (if x = (r : Q) then (1 : ℝ) else 0) *
      (if y = (r : Q) then (1 : ℝ) else 0)) ≤ if x=y then 1 else 0 := by
  by_cases hxy : x=y
  · subst y
    have hid (r : Qˣ) : (if x=(r : Q) then (1 : ℝ) else 0)*
        (if x=(r : Q) then (1 : ℝ) else 0) = if x=(r : Q) then 1 else 0 := by
      split_ifs <;> norm_num
    simp_rw [hid]
    simp only [ite_true]
    by_cases hu : IsUnit x
    · obtain ⟨u, rfl⟩ := hu
      simp only [Units.val_inj]
      simp
    · have hneq (u : Qˣ) : x ≠ (u : Q) := fun h => hu (h ▸ u.isUnit)
      simp only [hneq, if_false, Finset.sum_const_zero]
      norm_num
  · rw [if_neg hxy]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hx : x=(r : Q)
    · have hy : y≠(r : Q) := fun hy => hxy (hx.trans hy.symm)
      rw [if_pos hx,if_neg hy,mul_zero]
    · rw [if_neg hx,zero_mul]

theorem trace_residue_second_fourth_integral_le_count (a : 𝓞 K)
    [Fintype (PrincipalResidueRing a)] (x : α → 𝓞 K) (y : β → 𝓞 K) :
    (∫ q, (∑ r : (PrincipalResidueRing a)ˣ,
      ‖traceResidueWeylSum a 3 x (fun _ => 1) r q‖^2) *
      ‖traceWeylSum 3 y (fun _ => 1) (traceTorusMul a q)‖^4 ∂traceHaar) ≤
      (mixedResidueCongruentCount a x y : ℝ) := by
  let w := fun r : (PrincipalResidueRing a)ˣ => fun i : α =>
    if Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x i) = (r : PrincipalResidueRing a)
      then (1 : ℝ) else 0
  have hsum (r : (PrincipalResidueRing a)ˣ) (q : ArchimedeanTraceTorus K) :
      traceResidueWeylSum a 3 x (fun _ => 1) r q = traceWeylSum 3 x (fun i => (w r i : ℂ)) q := by
    simp only [traceResidueWeylSum,traceWeylSum,w]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [Finset.sum_mul,hsum]
  rw [integral_finset_sum]
  · change (∑ r : (PrincipalResidueRing a)ˣ,
      ∫ q, ‖traceWeylSum 3 x (fun i => (w r i : ℂ)) q‖^2 *
        ‖traceWeylSum 3 y (fun _ => ((1 : ℝ) : ℂ)) (traceTorusMul a q)‖^4 ∂traceHaar) ≤ _
    simp_rw [trace_second_fourth_integral]
    rw [Finset.sum_comm]
    have he : (mixedResidueCongruentCount a x y : ℝ) =
        ∑ t : (α × α) × ((β × β) × (β × β)),
          if Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.1) =
              Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.2) ∧
            mixedSecondFourthPhase a x y t = 0 then (1 : ℝ) else 0 := by
      unfold mixedResidueCongruentCount
      rw [Fintype.card_subtype,← Finset.sum_filter]
      simp
    rw [he]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hphase : mixedSecondFourthPhase a x y t=0
    · simpa [hphase,mixedSecondFourthCoefficient,w] using
        (unit_pair_indicators_sum_le (Q := PrincipalResidueRing a)
          (Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.1))
          (Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.2)))
    · simp [hphase]
  · intro r hr
    exact (((traceWeylSum_continuous _ _ _).norm.pow 2).mul
      (((traceWeylSum_continuous _ _ _).comp (traceTorusMul_continuous a)).norm.pow 4)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

#print axioms trace_second_fourth_integral
#print axioms trace_residue_second_fourth_integral_le_count
end WaringSiegel.WSL4Local
