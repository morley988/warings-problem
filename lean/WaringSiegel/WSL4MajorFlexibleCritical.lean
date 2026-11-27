import WaringSiegel.WSL4MajorFlexibleScale
import WaringSiegel.WSL3MomentCritical

/-! # Actual critical moments outside the smaller power-cutoff arcs -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module GafniTao
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_shrinking_critical_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (R : ℕ) (hR : 1≤R) (lam : ℝ) (hlam0 : 0≤lam) (hlam1 : lam≤1) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) (R+2) lam P,
        ‖compactTraceWeylSum (R+2) f hc P (by linarith) q‖^((R+2)*(R+3)) ∂traceHaar) ≤
        C*(P^finrank ℚ K)^(((R+2)^2:ℕ)+1-2*lam+ε : ℝ) := by
  let s := wooleyTriangular (R+2)
  have hs : 1≤s := by
    simpa only [wooleyTriangular_one] using wooleyTriangular_mono (show 1≤R+2 by omega)
  obtain ⟨B,A,hB,hA,hlocalized⟩ := compactTraceWeylSum_flexible_localized_moment f hc R s hR hs
  obtain ⟨J,hJ,hcount⟩ := numberField_critical_count_bound (K := K) (R+2) (by omega) hε
  let E : ℝ := (s:ℝ)+ε
  let D : ℝ := (A^finrank ℚ K)^E
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨B*J*D,by positivity,?_⟩
  intro P hP
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  obtain ⟨ht1,htP,htH,hPH⟩ := rpow_translation_window P hP R hR lam hlam0 hlam1
  obtain ⟨T,hT,hlocal⟩ := hlocalized P (P^lam) (P^(R+2)/P^lam) hP ht1 htP htH hPH
  have hj := hcount (A*P) (one_le_mul_of_one_le_of_one_le hA hP)
    (fun a : T => a.val) Subtype.val_injective (fun a v => hT a.val a.property v)
  have hscale : (((A*P)^finrank ℚ K):ℝ)^E = D*(P^finrank ℚ K)^E := by
    rw [mul_pow,Real.mul_rpow (by positivity) (by positivity)]
  change (vinogradovCount (R+2) s (fun a : T => a.val):ℝ)≤J*(((A*P)^finrank ℚ K):ℝ)^E at hj
  rw [hscale] at hj
  have ht : 2*s=(R+2)*(R+3) := by
    apply Nat.cast_injective (R := ℝ)
    dsimp [s]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    rw [wooleyTriangular_cast]
    push_cast
    ring
  have he : (wooleyTriangular R:ℝ)+(R+2:ℕ)-2*lam+E = (((R+2)^2:ℕ):ℝ)+1-2*lam+ε := by
    dsimp [E,s]
    push_cast
    rw [wooleyTriangular_cast,wooleyTriangular_cast]
    push_cast
    ring
  rw [← ht,shrinkingMinorArcs_eq_flexible _ _ _ hP0]
  calc
    _ ≤ B*(P^finrank ℚ K)^wooleyTriangular R*(P^(R+2)/P^lam)^finrank ℚ K/(P^lam)^finrank ℚ K*
        (vinogradovCount (R+2) s (fun a : T => a.val):ℝ) := hlocal
    _ ≤ B*(P^finrank ℚ K)^wooleyTriangular R*(P^(R+2)/P^lam)^finrank ℚ K/(P^lam)^finrank ℚ K*
        (J*(D*(P^finrank ℚ K)^E)) := mul_le_mul_of_nonneg_left hj (by positivity)
    _ = (B*J*D)*((P^finrank ℚ K)^wooleyTriangular R*(P^(R+2)/P^lam)^finrank ℚ K/
        (P^lam)^finrank ℚ K*(P^finrank ℚ K)^E) := by ring
    _ = _ := by rw [flexible_volume_scale P hP0,he]

theorem compactTraceWeylSum_shrinking_critical_bound_k
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k : ℕ) (hk : 3≤k) (lam : ℝ) (hlam0 : 0≤lam) (hlam1 : lam≤1) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k lam P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^(k*(k+1)) ∂traceHaar) ≤
        C*(P^finrank ℚ K)^((k^2:ℕ)+1-2*lam+ε : ℝ) := by
  have hR : 1≤k-2 := by omega
  have h2 : k-2+2=k := by omega
  have h3 : k-2+3=k+1 := by omega
  simpa only [h2,h3] using compactTraceWeylSum_shrinking_critical_bound f hc (k-2) hR lam hlam0 hlam1 hε

#print axioms compactTraceWeylSum_shrinking_critical_bound_k
end WaringSiegel.WSL4
