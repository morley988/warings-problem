import Waring.SeedCompletionNaturalChronological
import Waring.EndgameCompletionPolicySemanticsRecurrence
import Waring.EndgameCompletionPolicySemanticsMajor

/-! # The literal policy prefixes are the chronological source boxes -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPrefixStages
open Certificate PolicyCompletionMajorPowerRanges SeedCompletionNaturalBox SeedCompletionSourceBounds
open SmoothMoments

theorem prefixPhi_snoc (p : Policy) (j : ℕ) :
    prefixPhi p (j+1)=Fin.snoc (prefixPhi p j) (p.phi[j]!:ℝ) := by
  funext i
  refine Fin.lastCases ?_ (fun t=>?_) i
  · simp [prefixPhi]
  · simp [prefixPhi]

theorem prefixPhi_zero (p : Policy) : prefixPhi p 0=emptyPhi := by
  funext i
  exact Fin.elim0 i

theorem prefixPhi_pos {k : ℕ} {p : Policy} (hguard : PolicyAnalyticGuards k p)
    {j : ℕ} (hj : j≤p.phi.size) (i : Fin j) : 0<prefixPhi p j i :=
  phiReal_pos hguard ⟨i.val,i.isLt.trans_le hj⟩

theorem prefixPhi_shift_pos {k : ℕ} {p : Policy} (hk : 0<k) (hguard : PolicyAnalyticGuards k p)
    {j : ℕ} (hj : j≤p.phi.size) (i : Fin j) : 0<shiftExponents k (prefixPhi p j) i :=
  phiReal_shift_pos hk hguard ⟨i.val,i.isLt.trans_le hj⟩

theorem next_phi_constraints {k : ℕ} {p : Policy} (hk : 0<k)
    (hguard : PolicyAnalyticGuards k p) (hsize : p.phi.size<k)
    {j : ℕ} (hj : j<p.phi.size) :
    0≤(p.phi[j]!:ℝ) ∧ (k:ℝ)*(p.phi[j]!:ℝ)≤1 ∧
      total (prefixPhi p j)+(p.phi[j]!:ℝ)≤1 := by
  have hp:=phiReal_pos hguard ⟨j,hj⟩
  have hs:=phiReal_shift_pos hk hguard ⟨j,hj⟩
  have ht:=length_pos (show j+1<k by omega) (prefixPhi p (j+1))
    (fun i=>(prefixPhi_shift_pos hk hguard (by omega) i).le)
  have he : total (prefixPhi p (j+1))=total (prefixPhi p j)+(p.phi[j]!:ℝ) := by
    rw [←prefixTotal_cast_eq_total (by omega),prefixTotal_cast_succ hj]
  rw [he] at ht
  refine ⟨hp.le,?_,by linarith⟩
  unfold shiftExponents at hs
  change 0<1-(k:ℝ)*(p.phi[j]!:ℝ) at hs
  linarith

/-- One actual counted backward step has exactly the stored row exponent. -/
theorem policy_backward_step {k : ℕ} {p : Policy} {curve coefficient : Curve}
    {ev : Evaluation} (hshape : PolicyShapeAssociation k p)
    (hguard : PolicyAnalyticGuards k p)
    (hmom : PolicyMomentAssociation k curve coefficient p ev)
    (hcurve : AdmissibleCurve k curve) {j : ℕ} (hj : 1≤j) (hjlt : j<p.phi.size)
    {χ : ℝ}
    (hX : SourcePowerBound
      (powerBoxCross k p.path[j]! ((2:ℝ)^(j+1)) (prefixPhi p (j+1))) χ) :
    SourcePowerBound (powerBoxCross k p.path[j-1]! ((2:ℝ)^j) (prefixPhi p j))
      (((recurrenceRow k curve p j).1:ℝ)+max ((recurrenceRow k curve p j).2:ℝ) χ/2) := by
  have hk : 2≤k:=by have hh:=hshape.1; omega
  have hsize : p.phi.size<k:=by have hh:=hshape.2.2.2.1; omega
  have hu : 0<p.path[j]!:=hshape.2.2.2.2.2.2.1 ⟨j,hjlt⟩
  have hprev : j-1<p.phi.size-1:=by omega
  have hjpred : j-1+1=j:=by omega
  have hsplit' : p.path[j]!<2*p.path[j-1]!:=by
    simpa only [hjpred] using hshape.2.2.2.2.2.2.2.1 ⟨j-1,hprev⟩
  let u : ℕ:=p.path[j]!-1
  have hu1 : u+1=p.path[j]!:=by dsimp [u]; omega
  let t : ℕ:=2*p.path[j-1]!-p.path[j]!
  have hsplit : (u+1)+t=2*p.path[j-1]!:=by dsimp [t]; omega
  have hU : AdmissibleExponent k (2*(u+1)) ((moment curve (2*p.path[j]!)).getD 0:ℝ):=by
    rw [hu1]
    exact hmom.path_admissible hcurve ⟨j,hjlt⟩
  have hT : AdmissibleExponent k (2*t) ((moment curve (2*t)).getD 0:ℝ):=by
    simpa only [hjpred] using hmom.backward_admissible hcurve ⟨j-1,hprev⟩
  have hφ:=fun i=>(prefixPhi_pos hguard hjlt.le i).le
  have hh:=fun i=>(prefixPhi_shift_pos (by omega : 0<k) hguard hjlt.le i).le
  obtain ⟨hψ,hψk,hsum⟩:=next_phi_constraints (by omega : 0<k) hguard hsize hjlt
  have hnext : SourcePowerBound
      (powerBoxCross k (u+1) (2*(2:ℝ)^j) (Fin.snoc (prefixPhi p j) (p.phi[j]!:ℝ))) χ:=by
    rw [hu1,←prefixPhi_snoc]
    convert hX using 1 <;> rw [pow_succ] <;> ring
  have H:=backward_cross_power (prefixPhi p j) hk (by omega) (one_le_pow₀ (by norm_num))
    hφ hh hψ hψk hsum hsplit hU hT hnext
  have hur : (u:ℝ)+1=(p.path[j]!:ℝ):=by exact_mod_cast hu1
  rw [hur] at H
  convert H using 1
  rw [recurrenceRow_prefactor_cast k curve hjlt,recurrenceRow_diagonal_cast k curve hjlt]
  dsimp [parameterExponent,prefixAmplitude,t]
  push_cast
  ring

#print axioms policy_backward_step
end Waring.PolicyCompletionPrefixStages
