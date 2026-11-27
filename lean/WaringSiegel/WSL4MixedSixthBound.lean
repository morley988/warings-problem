import WaringSiegel.WSL4MixedMomentCount
import WaringSiegel.WSL4MixedCongruentBound
import WaringSiegel.WSL4WeilTraceComplete

/-! # An unconditional mixed-sixth bound on the original finite boxes

All complete-sum estimates are instantiated with the proved field constants.
-/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical nonZeroDivisors
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
  WaringSiegel.WSL4 WaringSiegel.WSL4Weil
variable {K : Type*} [Field K] [NumberField K]

theorem mixedSixthBoxIntegral_sum_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P M : ℝ), 1≤M → M^7≤P →
      ∀ X A Y : Finset (𝓞 K),
      (∀ x ∈ X, ‖mixedEmbedding K (x:K)‖≤P) →
      (∀ m ∈ A, ∀ v : InfinitePlace K, M≤v (m:K)) →
      (∀ m ∈ A, ‖mixedEmbedding K (m:K)‖≤2*M) →
      (∀ y ∈ Y, ‖mixedEmbedding K (y:K)‖≤P/M) →
      (∑m:A,mixedSixthBoxIntegral m.val X Y) ≤
        C*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
  have heps : 0<ε/4 := by positivity
  obtain ⟨CK,hCK,hkernel⟩ := mixedSixthBoxIntegral_sum_count_bound (K:=K) heps
  obtain ⟨CC,hCC,hcount⟩ := congruent_mixed_count_box_bound (K:=K) (ε/4) heps
    cubicTwistExceptionalConstant cubicTwistExceptionalConstant_pos
    fieldCenterCompleteSum_cubic_kappa_bound
  let D : ℝ := ((2:ℝ)^finrank ℚ K)^3
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨(CK*CC)*D^(ε/4),by positivity,?_⟩
  intro P M hM hMP X A Y hX hAlo hAhi hY
  have hM0 : 0<M := by linarith
  have hP0 : 0<P := lt_of_lt_of_le (pow_pos hM0 7) hMP
  have hA0 : ∀m∈A,m≠0 := by
    intro m hm hz
    let v : InfinitePlace K := Classical.choice inferInstance
    have hh := hAlo m hm v
    have hh' : M≤0 := by simpa [hz] using hh
    linarith
  have hb := hcount P M hM hMP X A Y hX hAlo hAhi hY
  have heR := congrArg (fun n:ℕ => (n:ℝ)) (congruent_mixed_count_diagonal_split X A Y hA0)
  push_cast at heR
  rw [heR] at hb
  have hk := hkernel (2*M) (by positivity) X A Y hA0 hAhi
  have hMP1 : M≤P := by
    have hh : M^1≤M^7 := pow_le_pow_right₀ hM (by norm_num)
    have hh' : M≤M^7 := by simpa only [pow_one] using hh
    exact hh'.trans hMP
  have hXY : M^finrank ℚ K≤P^finrank ℚ K := pow_le_pow_left₀ hM0.le hMP1 _
  have he : ((2*M)^finrank ℚ K)^3=D*(M^finrank ℚ K)^3 := by
    dsimp [D]
    rw [mul_pow,mul_pow]
  calc
    _ ≤ CK*(((2*M)^finrank ℚ K)^3:ℝ)^(ε/4) *
        (CC*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε/4)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ)) :=
      hk.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = (CK*CC)*(D*(M^finrank ℚ K)^3)^(ε/4)*
        ((P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε/4)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ)) := by
      rw [he]
      ring
    _ ≤ _ := mixed_kernel_epsilon_absorb (P^finrank ℚ K) (M^finrank ℚ K)
      (CK*CC) D ε (pow_pos hP0 _) (pow_nonneg hM0.le _) hXY
      (mul_nonneg hCK.le hCC.le) hD.le hε.le

theorem mixedSixthBoxIntegral_single_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P M : ℝ), 1≤M → M^7≤P →
      ∀ (m:𝓞 K) (X Y:Finset (𝓞 K)),
      (∀x∈X,‖mixedEmbedding K (x:K)‖≤P) →
      (∀v:InfinitePlace K,M≤v (m:K)) →
      ‖mixedEmbedding K (m:K)‖≤2*M →
      (∀y∈Y,‖mixedEmbedding K (y:K)‖≤P/M) →
      mixedSixthBoxIntegral m X Y ≤
        C*(P^finrank ℚ K:ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
  obtain ⟨C,hC,hbound⟩ := mixedSixthBoxIntegral_sum_bound (K:=K) ε hε
  refine ⟨C,hC,?_⟩
  intro P M hM hMP m X Y hX hmlo hmhi hY
  have hh := hbound P M hM hMP X {m} Y hX
    (by simpa only [Finset.mem_singleton,forall_eq] using hmlo)
    (by simpa only [Finset.mem_singleton,forall_eq] using hmhi) hY
  simpa using hh

#print axioms mixedSixthBoxIntegral_sum_bound
#print axioms mixedSixthBoxIntegral_single_bound
end WaringSiegel.WSL4Local
