import WaringSiegel.WSL4MixedPowerMask
import WaringSiegel.WSL4MixedCountSplit
import WaringSiegel.WSL2MomentDivisorBridge
import WaringSiegel.WSL2UnitTransport

/-! # Uniform reduction of the literal mixed sixth moment to its original box count -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

def mixedSixthBoxIntegral (m : 𝓞 K) (X Y : Finset (𝓞 K)) : ℝ :=
  ∫q, ‖traceCoprimeWeylSum m 3 (fun x : X => x.val) (fun _ => 1) q‖^2 *
    ‖traceWeylSum 3 (fun y : Y => y.val) (fun _ => 1) (traceTorusMul (m^3) q)‖^4 ∂traceHaar

theorem mixedSixthBoxIntegral_nonneg (m : 𝓞 K) (X Y : Finset (𝓞 K)) :
    0≤mixedSixthBoxIntegral m X Y :=
  integral_nonneg (fun q => mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) 4))

theorem mixedSixthBoxIntegral_count_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (m : 𝓞 K), m≠0 → ∀ (M : ℝ), 0≤M →
      ‖mixedEmbedding K (m:K)‖≤M → ∀ X Y : Finset (𝓞 K),
      mixedSixthBoxIntegral m X Y ≤ C*((M^finrank ℚ K)^3:ℝ)^ε *
        (mixedResidueCongruentCount (m^3) (fun x : X => x.val) (fun y : Y => y.val):ℝ) := by
  obtain ⟨C,hC,hbound⟩ := trace_coprime_mixed_sixth_le_congruent_count (K:=K) hε
  refine ⟨C,hC,fun m hm M hM hmM X Y => ?_⟩
  have hm3 : m^3≠0 := pow_ne_zero _ hm
  letI := idealResidueFintype (Ideal.span ({m^3}:Set (𝓞 K)))
    (mt Ideal.span_singleton_eq_bot.mp hm3)
  letI := traceTorusMul_kernel_finite_type (m^3) hm3
  letI : Fintype (traceTorusMul (m^3)).ker := Fintype.ofFinite _
  have hh := hbound (m^3) hm3 (fun x : X => x.val) (fun y : Y => y.val)
  simp only [traceCoprimeWeylSum_power_modulus m 3 (by norm_num)] at hh
  have hn : ((Ideal.absNorm (Ideal.span ({m^3}:Set (𝓞 K)))):ℝ)≤(M^finrank ℚ K)^3 := by
    have ha := absNorm_le_box (K:=K) (a:=m) hM (fun v =>
      (by rw [← normAtPlace_apply]; exact (normAtPlace_le_mixed_norm _ v).trans hmM))
    have hb := pow_le_pow_left₀ (absNorm_nonneg m) ha 3
    rw [Ideal.absNorm_span_singleton,Int.cast_natAbs,Int.cast_abs]
    change absNorm (m^3)≤_
    rw [absNorm_pow]
    exact hb
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hn hε.le) hC.le)
    (Nat.cast_nonneg _)

theorem mixedSixthBoxIntegral_sum_count_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M : ℝ), 0≤M → ∀ X A Y : Finset (𝓞 K),
      (∀ m∈A, m≠0) → (∀ m∈A, ‖mixedEmbedding K (m:K)‖≤M) →
      (∑m:A,mixedSixthBoxIntegral m.val X Y) ≤ C*((M^finrank ℚ K)^3:ℝ)^ε *
        (A.card*X.card*cubicFourthBoxCount Y + mixedCongruentOffdiagonalCount X A Y : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := mixedSixthBoxIntegral_count_bound (K:=K) hε
  refine ⟨C,hC,fun M hM X A Y hA hAM => ?_⟩
  have hh := Finset.sum_le_sum (s:=(Finset.univ : Finset A)) (fun (m:A) (_ : m∈Finset.univ) =>
    hbound m.val (hA m.val m.property) M hM (hAM m.val m.property) X Y)
  rw [← Finset.mul_sum] at hh
  have he := congruent_mixed_count_diagonal_split X A Y hA
  have heR := congrArg (fun n : ℕ => (n:ℝ)) he
  push_cast at heR
  rw [heR] at hh
  exact hh

#print axioms mixedSixthBoxIntegral_count_bound
#print axioms mixedSixthBoxIntegral_sum_count_bound
end WaringSiegel.WSL4Local
