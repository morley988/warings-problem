import Waring.EndgameCompletionMinorReproduction
import Waring.EndgameCompletionMinorSeparation

/-!
# Reciprocal averaging of the actual projected slices

Exact Dirichlet reproduction is combined with the proved short-multiple
separation on the literal ordinary minor region. All coefficient integrals
retain their original normalization.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion
open FourierCompletion QuadraticModulation

theorem dirichlet_cap_scale (r s N : ℕ) (hN : 1≤N) :
    ((2*(s*(2*N)^(r+1))+1 : ℕ) : ℝ)≤
      ((2*s*2^(r+1)+1 : ℕ) : ℝ)*(N : ℝ)^(r+1) := by
  have hn : (1 : ℝ)≤(N : ℝ)^(r+1) := one_le_pow₀ (by exact_mod_cast hN)
  push_cast
  rw [mul_pow]
  nlinarith

theorem projectedSlice_average_minor (r s : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ∀ θ : ℝ,
      θ∈Set.Ioc 0 1 → θ∉ordinaryBroadMajor (r+2) N →
      (N : ℝ)⁻¹*(∑ y∈Finset.Icc 1 N,
        projectedSlice r s (2*N) (-((r+2 : ℕ) : ℝ)*(y : ℝ)*θ) θ)≤
      C*(N : ℝ)^((r : ℝ)+ε)*
        (∫ t in (0 : ℝ)..1,projectedSlice r s (2*N) t θ) := by
  let L : ℝ := ((2*s*2^(r+1)+1 : ℕ) : ℝ)
  have hL : 1≤L := by dsimp [L]; exact_mod_cast Nat.le_add_left 1 _
  obtain ⟨C,hC,hbound⟩ := ordinary_minor_reciprocal_average (r+2) (by omega) L hL hε
  refine ⟨C,hC,?_⟩
  intro N hN θ hθ hm
  let H : ℕ := s*(2*N)^(r+1)
  let band := Finset.Icc (-(H : ℤ)) (H : ℤ)
  let F := fun t=>projectedSlice r s (2*N) t θ
  let K := fun (y : ℕ) (t : ℝ)=>‖kernel band (t+((r+2 : ℕ) : ℝ)*y*θ)‖
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hFc : Continuous F := by
    change Continuous (fun t : ℝ=>projectedMoment r s (positiveNode (2*N))
      (fun n=>e (θ*(positiveNode (2*N) n : ℝ)^(r+2)+t*(positiveNode (2*N) n : ℝ)^(r+1))))
    apply continuous_projectedMoment r s (positiveNode (2*N))
    intro n
    apply continuous_e.comp
    fun_prop
  have hKc (y : ℕ) : Continuous (K y) := (continuous_kernel band).norm.comp
    (show Continuous (fun t : ℝ=>t+((r+2 : ℕ) : ℝ)*y*θ) from
      continuous_id.add continuous_const)
  have hFi : IntervalIntegrable F volume 0 1 := hFc.intervalIntegrable 0 1
  have hKi (y : ℕ) : IntervalIntegrable (fun t=>F t*K y t) volume 0 1 :=
    (hFc.mul (hKc y)).intervalIntegrable 0 1
  have hKbound (t : ℝ) : (N : ℝ)⁻¹*(∑ y∈Finset.Icc 1 N,K y t)≤
      C*(N : ℝ)^((r : ℝ)+ε) := by
    have hc := hbound N hN θ t hθ hm
    have he : ((r+2 : ℕ) : ℝ)-2+ε=(r : ℝ)+ε := by push_cast; ring
    rw [he] at hc
    apply le_trans _ hc
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNpos.le)
    apply Finset.sum_le_sum
    intro y _
    have hh := dirichlet_kernel_le_real_cap H (L*(N : ℝ)^(r+1))
      (t+((r+2 : ℕ) : ℝ)*y*θ) (by positivity) (dirichlet_cap_scale r s N hN)
    simpa only [K,band,add_comm t _] using hh
  have hrep (y : ℕ) : F (-((r+2 : ℕ) : ℝ)*(y : ℝ)*θ)≤
      ∫ t in (0 : ℝ)..1,F t*K y t := by
    have hh := projectedSlice_reproduction r s (2*N)
      (-((r+2 : ℕ) : ℝ)*(y : ℝ)*θ) θ
    simpa only [F,K,band,H,neg_mul,sub_neg_eq_add] using hh
  calc
    _ ≤ (N : ℝ)⁻¹*(∑ y∈Finset.Icc 1 N,∫ t in (0 : ℝ)..1,F t*K y t) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _=>hrep y))
        (inv_nonneg.mpr hNpos.le)
    _ = ∫ t in (0 : ℝ)..1,F t*((N : ℝ)⁻¹*∑ y∈Finset.Icc 1 N,K y t) := by
      rw [← intervalIntegral.integral_finset_sum (fun y _=>hKi y),
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∫ t in (0 : ℝ)..1,F t*(C*(N : ℝ)^((r : ℝ)+ε)) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        ((hFc.mul (continuous_const.mul
          (continuous_finset_sum _ (fun y _=>hKc y)))).intervalIntegrable 0 1)
        (hFi.mul_const _)
      intro t _
      exact mul_le_mul_of_nonneg_left (hKbound t) (projectedSlice_nonneg r s (2*N) t θ)
    _ = _ := by rw [intervalIntegral.integral_mul_const]; ring

/-- The completed lower-degree mean is bounded by the full next-coefficient
mean with the exact minor saving and completion mass. -/
theorem projectedSlice_minor_bound (r s : ℕ) (hr : 1≤r) (hs : 1≤s)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ∀ θ : ℝ,
      θ∈Set.Ioc 0 1 → θ∉ordinaryBroadMajor (r+2) N →
      projectedSlice r s N 0 θ≤completionMass N^(2*s)*
        (C*(N : ℝ)^((r : ℝ)+ε)*
          (∫ t in (0 : ℝ)..1,projectedSlice r s (2*N) t θ)) := by
  obtain ⟨C,hC,hbound⟩ := projectedSlice_average_minor r s hε
  refine ⟨C,hC,?_⟩
  intro N hN θ hθ hm
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hsum := Finset.sum_le_sum (s := Finset.Icc 1 N)
    (fun y hy=>projected_interval_completion r s N y hr hs (Finset.mem_Icc.mp hy).2 θ)
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hNpos.le)
  rw [← mul_assoc,inv_mul_cancel₀ hNpos.ne',one_mul] at hh
  calc
    _ ≤ completionMass N^(2*s)*((N : ℝ)⁻¹*
        ∑ y∈Finset.Icc 1 N,
          projectedSlice r s (2*N) (-((r+2 : ℕ) : ℝ)*(y : ℝ)*θ) θ) := by
      convert hh using 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound N hN θ hθ hm)
      (pow_nonneg (completionMass_nonneg N) _)

#print axioms projectedSlice_average_minor
#print axioms projectedSlice_minor_bound
end Waring.EndgameCompletion
