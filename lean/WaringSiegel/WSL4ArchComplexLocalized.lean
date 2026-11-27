import WaringSiegel.WSL4ArchComplexFamilies
import WaringSiegel.WSL3UnitComplexDyadic

/-! # Uniform localized saddle estimate for compact amplitude families -/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
set_option maxHeartbeats 1000000

/-- Dyadic summation retains one constant over the whole compact family. -/
theorem uniform_complex_localized_stationary_family {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T)
    (hFnorm : ∀ p ∈ T, ∀ z, ‖F (p,z)‖ ≤ 1)
    {a0 A : ℝ} (ha0 : 0 < a0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ a t : ℂ,
      a0 ≤ ‖a‖ → ‖a‖ ≤ A → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖complexLocalizedIntegral (fun z => F (p,z))
          (a0/8) a t lambda‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := uniform_complex_shell_bound_family (A := A) hF hT ha0
  refine ⟨volume.real (closedBall (0:ℂ) 2)+2*C+1,by positivity,?_⟩
  intro p hp a t ha hA ht lambda hl
  let W : ℂ → ℂ := fun z => F (p,z)
  have hW : ContDiff ℝ ∞ W := hF.comp (contDiff_const.prodMk contDiff_id)
  have hWnorm : ∀ z, ‖W z‖ ≤ 1 := hFnorm p hp
  let delta := (Real.sqrt lambda)⁻¹
  have hs : 0 < Real.sqrt lambda := Real.sqrt_pos.mpr hl
  have hd : 0 < delta := inv_pos.mpr hs
  have hdid : lambda*delta^2 = 1 := by
    dsimp only [delta]
    rw [inv_pow,Real.sq_sqrt hl.le,mul_inv_cancel₀ hl.ne']
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(a0/8)/delta)
  have hpow : (N:ℝ) ≤ (2:ℝ)^N := by
    exact_mod_cast (show N < 2^N from Nat.lt_two_pow_self).le
  have hN' : 2*(a0/8) ≤ (2:ℝ)^N*delta := by
    have hdN := (div_lt_iff₀ hd).mp hN
    exact hdN.le.trans (mul_le_mul_of_nonneg_right hpow hd.le)
  have hdecomp := complexLocalizedIntegral_dyadic hW (by positivity : 0 < a0/8) hd a t lambda hN'
  have hi := complexInnerIntegral_bound hWnorm (a0/8) a t lambda hd
  have hi' : lambda*‖complexInnerIntegral W (a0/8) a t lambda delta‖ ≤
      volume.real (closedBall (0:ℂ) 2) := by
    have h := mul_le_mul_of_nonneg_left hi hl.le
    simpa only [← mul_assoc,hdid,one_mul] using h
  have hshell : ∀ j : ℕ,
      lambda*‖complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta)‖ ≤ C*(1/2:ℝ)^j := by
    intro j
    have h := hb p hp a t ha hA ht lambda ((2:ℝ)^j*delta) hl (by positivity)
    have hp : 0 < (2:ℝ)^j := by positivity
    have he : lambda^2*((2:ℝ)^j*delta)^2 = (2:ℝ)^(2*j)*lambda := by
      calc
        _ = (2:ℝ)^(2*j)*lambda*(lambda*delta^2) := by
          rw [Nat.mul_comm 2 j,pow_mul]
          ring
        _ = _ := by rw [hdid,mul_one]
    rw [he,mul_assoc] at h
    have hhalf : (2:ℝ)^(2*j)*(1/2:ℝ)^j = (2:ℝ)^j := by
      rw [show 2*j=j+j by omega,pow_add,mul_assoc,← mul_pow]
      norm_num
    have hge : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    apply (mul_le_mul_left (by positivity : 0 < (2:ℝ)^(2*j))).mp
    calc
      _ ≤ C := h
      _ ≤ C*(2:ℝ)^j := le_mul_of_one_le_right hC.le hge
      _ = _ := by rw [← mul_assoc,mul_comm ((2:ℝ)^(2*j)) C,mul_assoc,hhalf]
  have hn := norm_add_le (complexInnerIntegral W (a0/8) a t lambda delta)
    (∑ j ∈ Finset.range N, complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta))
  rw [hdecomp]
  have hsum := norm_sum_le (s := Finset.range N)
    (f := fun j => complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta))
  have hsum' : lambda*(∑ j ∈ Finset.range N,
      ‖complexShellIntegral W (a0/8) a t lambda ((2:ℝ)^j*delta)‖) ≤ 2*C := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range N, C*(1/2:ℝ)^j := Finset.sum_le_sum (fun j _ => hshell j)
      _ = C*(∑ j ∈ Finset.range N, (1/2:ℝ)^j) := (Finset.mul_sum _ _ _).symm
      _ ≤ C*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le N) hC.le
      _ = _ := by ring
  nlinarith

#print axioms uniform_complex_localized_stationary_family
end WaringSiegel.WSL4
