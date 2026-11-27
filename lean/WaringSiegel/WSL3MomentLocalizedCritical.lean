import WaringSiegel.WSL3MomentLocalized
import WaringSiegel.WSL3MomentCritical

/-! # The critical localized moment has a full volume saving -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module GafniTao
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- For k≥3, the actual k(k+1)-st minor-arc moment is bounded by
C X^(k²-1+epsilon), uniformly in scale. -/
theorem compactTraceWeylSum_localized_critical_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (R : ℕ) (hR : 1 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) (R+2) P,
        ‖compactTraceWeylSum (R+2) f hc P (by linarith) q‖^((R+2)*(R+3)) ∂traceHaar) ≤
        C * (P^finrank ℚ K)^(((R+2)^2:ℕ)-1+ε : ℝ) := by
  let s := wooleyTriangular (R+2)
  have hs : 1 ≤ s := by
    simpa only [wooleyTriangular_one] using
      wooleyTriangular_mono (show 1 ≤ R+2 by omega)
  obtain ⟨B, A, hB, hA, hlocalized⟩ := compactTraceWeylSum_localized_moment_bound f hc R s hR hs
  obtain ⟨J, hJ, hcount⟩ := numberField_critical_count_bound (K := K) (R+2) (by omega) hε
  let E : ℝ := (s:ℝ)+ε
  let D : ℝ := (A^finrank ℚ K)^E
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B*J*D, by positivity, ?_⟩
  intro P hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  obtain ⟨T, hT, hlocal⟩ := hlocalized P hP
  have hj := hcount (A*P) (one_le_mul_of_one_le_of_one_le hA hP)
    (fun a : T => a.val) Subtype.val_injective (fun a v => hT a.val a.property v)
  have hscale : (((A*P)^finrank ℚ K):ℝ)^E = D*(P^finrank ℚ K)^E := by
    rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
  change (vinogradovCount (R+2) s (fun a : T => a.val) : ℝ) ≤ J*(((A*P)^finrank ℚ K):ℝ)^E at hj
  rw [hscale] at hj
  have ht : 2*s=(R+2)*(R+3) := by
    apply Nat.cast_injective (R := ℝ)
    dsimp [s]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    rw [wooleyTriangular_cast]
    push_cast
    ring
  have he : ((wooleyTriangular R+R:ℕ):ℝ)+E = (((R+2)^2:ℕ):ℝ)-1+ε := by
    dsimp [E, s]
    push_cast
    rw [wooleyTriangular_cast, wooleyTriangular_cast]
    push_cast
    ring
  rw [← ht]
  calc
    _ ≤ B*(P^finrank ℚ K)^(wooleyTriangular R+R) *
        (vinogradovCount (R+2) s (fun a : T => a.val) : ℝ) := hlocal
    _ ≤ B*(P^finrank ℚ K)^(wooleyTriangular R+R) * (J*(D*(P^finrank ℚ K)^E)) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = (B*J*D) * ((P^finrank ℚ K)^((wooleyTriangular R+R:ℕ):ℝ) * (P^finrank ℚ K)^E) := by
      rw [Real.rpow_natCast]
      ring
    _ = _ := by rw [← Real.rpow_add (by positivity), he]

#print axioms compactTraceWeylSum_localized_critical_bound
end WaringSiegel.WSL3
