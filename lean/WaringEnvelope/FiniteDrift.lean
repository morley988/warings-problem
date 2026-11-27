import WaringEnvelope.IndexedStages
import WaringEnvelope.PotentialIntegral
import Mathlib.Topology.Order.Lattice

/-! # The optimal finite drift from the actual certified stages -/
noncomputable section
namespace WaringEnvelope
open Set MeasureTheory
open scoped BigOperators
namespace IndexedStages
variable {C k z₀ z m R} (p : IndexedStages C k z₀ z m R)

def heightAt (i : ℕ) : ℝ := (p.height i:ℝ)/T
def lengthAt (i : ℕ) : ℝ := length (p.modulus i)
def rowDrift (i : ℕ) (t : ℝ) := min (p.heightAt i) (p.lengthAt i*t/2)
def drift (t : ℝ) : ℝ :=
  (Finset.range (p.N+1)).sup' ⟨0,Finset.mem_range.mpr (by omega)⟩ (fun i => p.rowDrift i t)

theorem row_le_drift (i : ℕ) (hi : i≤p.N) (t : ℝ) :
    p.rowDrift i t≤p.drift t := Finset.le_sup' (fun j => p.rowDrift j t) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

theorem exists_active (t : ℝ) : ∃ i≤p.N, p.drift t=p.rowDrift i t := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' (s:=Finset.range (p.N+1))
    ⟨0,Finset.mem_range.mpr (by omega)⟩ (fun i => p.rowDrift i t)
  exact ⟨i,Nat.lt_succ_iff.mp (Finset.mem_range.mp hi),he⟩

theorem continuous_drift : Continuous p.drift := by
  apply Continuous.finset_sup'_apply
  intro i _
  exact continuous_const.min ((continuous_const.mul continuous_id).div_const 2)

theorem positive_height (i : ℕ) (hi : i≤p.N) : 0<p.heightAt i := by
  have hp : (0:ℝ)<p.height i := by exact_mod_cast p.posHeight i hi
  exact div_pos hp (by norm_num [T])

theorem positive_length (i : ℕ) (hi : i≤p.N) : 0<p.lengthAt i := by
  have hp : (0:ℝ)<p.modulus i := by exact_mod_cast (show 0<B by decide).trans_le (p.posModulus i hi)
  exact div_pos (mul_pos (by norm_num [U]) hp) (by norm_num [V,B])

theorem positive_drift (t : ℝ) (ht : 0<t) : 0<p.drift t :=
  (lt_min (p.positive_height 0 (by omega)) (div_pos (mul_pos (p.positive_length 0 (by omega)) ht)
    (by norm_num))).trans_le (p.row_le_drift 0 (by omega) t)

theorem monotone_drift : Monotone p.drift := by
  intro x y hxy
  obtain ⟨i,hi,h⟩ := p.exists_active x
  rw [h]
  apply le_trans _ (p.row_le_drift i hi y)
  exact min_le_min le_rfl (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hxy (p.positive_length i hi).le) (by norm_num))

theorem drift_integral_bound (D dstar : ℝ) (hd : 0<dstar)
    (hstart : 2*p.heightAt 0/p.lengthAt 0≤D)
    (hstop : 2*p.heightAt p.N/p.lengthAt p.N≤dstar) :
    (∫ t in dstar..D, 1/p.drift t)≤D/p.heightAt 0-2/p.lengthAt p.N+R := by
  have h := potential_integral_bound p.drift p.heightAt p.lengthAt p.N D dstar
    p.continuous_drift.continuousOn p.positive_drift p.positive_height p.positive_length
    (fun i hi => div_le_div_of_nonneg_right (by exact_mod_cast (p.decreasing i hi).le)
      (by exact_mod_cast (Nat.zero_le T)))
    (fun i hi => div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast p.increasing i hi) (Nat.cast_nonneg U)) (by positivity))
    (fun i hi t _ => p.row_le_drift i hi t) hstart hstop
  have he : (∑ i∈Finset.range p.N, 2/p.lengthAt i*Real.log (p.heightAt i/p.heightAt (i+1)))=R := by
    refine Eq.trans ?_ p.cost
    apply Finset.sum_congr rfl
    intro i _
    have heq : p.heightAt i/p.heightAt (i+1)=(p.height i:ℝ)/p.height (i+1) := by
      exact div_div_div_cancel_right₀ (by norm_num [T] : (T:ℝ)≠0) _ _
    rw [heq];unfold lengthAt;ring
  rwa [he] at h

#print axioms continuous_drift
#print axioms drift_integral_bound
end IndexedStages
end WaringEnvelope
