import WaringSiegel.WSL3MomentProductMinor
import WaringSiegel.WSL3PoissonMixedFourierProducts
import WaringSiegel.WSL3UnitSmoothCutoff

/-!
# Exact compact product Fourier coefficients and actual representations

Finite orthogonality is carried out on the actual trace torus and the
literal compact integer supports. Nonvanishing gives a genuine tuple in
those supports. A fixed positive root box then supplies the positivity and
norm control in the exact Waring-Siegel target definition.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusCharacter_sum_frequency {ι : Type*} [Fintype ι]
    (a : ι → 𝓞 K) (q : ArchimedeanTraceTorus K) :
    traceTorusCharacter (∑ i, a i) q = ∏ i, traceTorusCharacter (a i) q := by
  simp only [traceTorusCharacter,map_sum,latticeCharacter_sum]

theorem traceWeylSum_product_fourier_coefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (k : ℕ) (nodes : ∀ i, α i → 𝓞 K) (w : ∀ i, α i → ℂ) (target : 𝓞 K) :
    (∫ q, (∏ i, traceWeylSum k (nodes i) (w i) q)*traceTorusCharacter (-target) q ∂traceHaar) =
      ∑ x : ∀ i, α i, if (∑ i, nodes i (x i)^k)=target then ∏ i, w i (x i) else 0 := by
  have he (q : ArchimedeanTraceTorus K) :
      (∏ i, traceWeylSum k (nodes i) (w i) q)*traceTorusCharacter (-target) q =
        traceFrequencySum (fun x : ∀ i, α i => (∑ i, nodes i (x i)^k)-target)
          (fun x => ∏ i, w i (x i)) q := by
    simp only [traceWeylSum]
    rw [Fintype.prod_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.prod_mul_distrib,← traceTorusCharacter_sum_frequency]
    rw [mul_assoc,← traceTorusCharacter_add_frequency]
    simp only [sub_eq_add_neg]
  simp_rw [he]
  rw [traceFrequencySum_integral]
  simp only [sub_eq_zero]

theorem compactTraceWeylSum_product_fourier_coefficient
    (k s : ℕ) (f : Fin s → mixedSpace K → ℂ)
    (hc : ∀ i, HasCompactSupport (f i)) (P : ℝ) (hP : P≠0) (target : 𝓞 K) :
    (∫ q, (∏ i, compactTraceWeylSum k (f i) (hc i) P hP q)*
      traceTorusCharacter (-target) q ∂traceHaar) =
      ∑ x : ∀ i, compactIntegerSupport (f i) (hc i) P hP,
        if (∑ i, (x i).val^k)=target then
          ∏ i, f i (P⁻¹ • mixedEmbedding K ((x i).val:K)) else 0 := by
  exact traceWeylSum_product_fourier_coefficient k
    (fun i (x : compactIntegerSupport (f i) (hc i) P hP) => x.val)
    (fun i (x : compactIntegerSupport (f i) (hc i) P hP) =>
      f i (P⁻¹ • mixedEmbedding K (x.val:K))) target

theorem compactTraceWeylSum_fourier_ne_zero_has_solution
    (k s : ℕ) (f : Fin s → mixedSpace K → ℂ)
    (hc : ∀ i, HasCompactSupport (f i)) (P : ℝ) (hP : P≠0) (target : 𝓞 K)
    (hne : (∫ q, (∏ i, compactTraceWeylSum k (f i) (hc i) P hP q)*
      traceTorusCharacter (-target) q ∂traceHaar) ≠ 0) :
    ∃ x : Fin s → 𝓞 K,
      (∀ i, f i (P⁻¹ • mixedEmbedding K (x i:K)) ≠ 0) ∧ ∑ i, x i^k=target := by
  by_contra hnone
  apply hne
  rw [compactTraceWeylSum_product_fourier_coefficient]
  apply Finset.sum_eq_zero
  intro x _
  have hn : (∑ i, (x i).val^k)≠target := by
    intro he
    apply hnone
    exact ⟨fun i => (x i).val,
      fun i => (mem_compactIntegerSupport _ _ _ _ _).mp (x i).property,he⟩
  rw [if_neg hn]

theorem representable_of_compactTraceFourier_ne_zero
    (k s : ℕ) (hk : 0<k) (target : 𝓞 K) (htarget : target≠0)
    (f : Fin s → mixedSpace K → ℂ) (hc : ∀ i, HasCompactSupport (f i))
    (ρ R : ℝ) (hρ : 0<ρ)
    (hsupport : ∀ i, Function.support (f i) ⊆ rootBox K ρ R)
    (hne : (∫ q, (∏ i, compactTraceWeylSum k (f i) (hc i) (rootScale k target)
      (rootScale_pos htarget k).ne' q)*traceTorusCharacter (-target) q ∂traceHaar) ≠ 0) :
    RepresentableByAtMost k s (R^finrank ℚ K) target := by
  obtain ⟨x,hx,hsum⟩ := compactTraceWeylSum_fourier_ne_zero_has_solution k s f hc
    (rootScale k target) (rootScale_pos htarget k).ne' target hne
  have hbox (i : Fin s) : x i ∈ scaledIntegerNodeSet (rootScale k target) ρ R :=
    hsupport i (hx i)
  refine ⟨s,le_rfl,x,?_,hsum,?_⟩
  · intro i σ
    exact (scaledIntegerNodeSet_positive (rootScale_pos htarget k) hρ (hbox i) σ).le
  · intro i
    exact scaledIntegerNodeSet_target_norm_bound k hk htarget (hbox i)

#print axioms compactTraceWeylSum_product_fourier_coefficient
#print axioms compactTraceWeylSum_fourier_ne_zero_has_solution
#print axioms representable_of_compactTraceFourier_ne_zero
end WaringSiegel.WSL3
