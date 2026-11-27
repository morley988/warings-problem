import WaringSiegel.WSL4CoprimeCubicScaled
import WaringSiegel.WSL4SmoothMixedSources

/-! # The prime-uniform square bound on the original broad minor arcs -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical ContDiff
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryBroadConstant (K : Type*) [Field K] [NumberField K] (R : ℝ) : ℝ :=
  (6*max 1 (2*R))^finrank ℚ K

theorem auxiliaryBroadConstant_ge_one (R : ℝ) : 1≤auxiliaryBroadConstant K R := by
  apply one_le_pow₀
  have hh : (1:ℝ)≤max 1 (2*R) := le_max_left _ _
  linarith

theorem square_bound_of_quartic_bound (a C X ε : ℝ) (hC : 0≤C) (hX : 0<X)
    (h : a^4≤C*X^(3+2*ε)) :
    a^2≤(C+1)*X^((3:ℝ)/2+ε) := by
  have he : ((C+1)*X^((3:ℝ)/2+ε))^2=(C+1)^2*X^(3+2*ε) := by
    rw [mul_pow,← Real.rpow_mul_natCast hX.le]
    congr 2
    ring
  apply (sq_le_sq₀ (sq_nonneg a) (by positivity)).mp
  rw [he,← pow_mul]
  exact h.trans (mul_le_mul_of_nonneg_right (by nlinarith) (Real.rpow_nonneg hX.le _))

theorem smoothCoprimeCubicSum_minor_square_bound
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ), 1≤P → ∀p:ℕ,p.Prime →
      ∀q:ArchimedeanTraceTorus K,
      q∉traceMajorArcUnion (P^3) (auxiliaryBroadConstant K R*P^finrank ℚ K) →
      ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz ρ R hρ hR) P p q 0‖^2 ≤
        C*(P^finrank ℚ K:ℝ)^((3:ℝ)/2+ε) := by
  have hd : 0<(finrank ℚ K:ℝ) := by exact_mod_cast (finrank_pos : 0<finrank ℚ K)
  have hε' : 0<2*(finrank ℚ K:ℝ)*ε := by positivity
  obtain ⟨C,hC,hbound⟩ := compactCoprimeTraceCubicSum_compact_minor_fourth_bound (K:=K)
    ((smoothWeightSchwartz ρ R hρ hR).smooth (⊤ : ℕ∞))
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
    (max 1 (2*R)) (le_max_left _ _)
    (fun x hx => (smoothWeightSchwartz_support_norm ρ R hρ hR x hx).trans (le_max_right _ _)) hε'
  refine ⟨C+1,by positivity,?_⟩
  intro P hP p hp q hq
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hb := hbound P hP p hp q 0 hq
  have he : (P^finrank ℚ K)^3*P^(2*(finrank ℚ K:ℝ)*ε) =
      (P^finrank ℚ K:ℝ)^(3+2*ε) := by
    rw [show 2*(finrank ℚ K:ℝ)*ε=(finrank ℚ K:ℝ)*(2*ε) by ring,
      Real.rpow_natCast_mul hP0.le,← Real.rpow_natCast (P^finrank ℚ K) 3,
      ← Real.rpow_add (pow_pos hP0 _)]
    norm_num
  apply square_bound_of_quartic_bound _ C _ ε hC.le (pow_pos hP0 _)
  rw [mul_assoc,he] at hb
  exact hb

#print axioms smoothCoprimeCubicSum_minor_square_bound
end WaringSiegel.WSL4Local
