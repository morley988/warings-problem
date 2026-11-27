import Waring.CertificateHeight
import Waring.NormalizedCubeCoefficient

/-! # Exact equality of the certificate savings and the proved source caps -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionResourceFormula
open Certificate NormalizedCoefficient ResourceScales

theorem minQ_three (a b c : Q) : minQ #[a,b,c]=some (qmin (qmin a b) c) := by
  simp [minQ,qmin]

theorem resourceSizeCap_coefficient (k : ℕ) (p : Policy) (r : Resource)
    (hkind : r.kind=.refined ∨ r.kind=.cube) :
    (resourceSizeCap k p r:ℝ)=
      min (min (2*(k:ℝ)*(p.phi[r.factor-1]!:ℝ))
        ((k:ℝ)-3-(k:ℝ)*(sumQ p.phi:ℝ)+(k:ℝ)*(p.phi[r.factor-1]!:ℝ)))
        (((k:ℝ)-6-(k:ℝ)*(sumQ p.phi:ℝ)+6*(k:ℝ)*(p.phi[r.factor-1]!:ℝ))/2) := by
  rcases hkind with hkind|hkind <;>
    simp only [resourceSizeCap,resourceSizeCaps,hkind,minQ_three,Option.getD_some,cast_qmin,q,
      Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]

theorem resourceReal_refined (k : ℕ) (p : Policy) (coefficient : Curve) (r : Resource)
    (hkind : r.kind=.refined) (ell : ℝ) :
    resourceReal k p coefficient r ell=
      refinedSaving k (sumQ p.phi:ℝ) (p.phi[r.factor-1]!:ℝ) ell
        ((delta (2*k) coefficient r.order).getD 0:ℝ) := by
  rw [resourceReal,hkind,resourceSizeCap_coefficient k p r (Or.inl hkind)]
  simp only [resourceLoss,Rat.cast_mul,q,Rat.cast_natCast,Rat.cast_ofNat]
  rw [refinedSaving,fourCap_coefficient_identity]
  simp only [min_assoc]

theorem resourceReal_cube (k : ℕ) (p : Policy) (coefficient : Curve) (r : Resource)
    (hkind : r.kind=.cube) (ell : ℝ) :
    resourceReal k p coefficient r ell=
      cubeSaving k (sumQ p.phi:ℝ) (p.phi[r.factor-1]!:ℝ) ell
        ((delta (2*k) coefficient r.order).getD 0:ℝ) := by
  rw [resourceReal,hkind,resourceSizeCap_coefficient k p r (Or.inr hkind)]
  simp only [resourceLoss,Rat.cast_mul,q,Rat.cast_natCast,Rat.cast_ofNat]
  unfold cubeSaving cubeFourCap
  have ht : (2*(k:ℝ)*(p.phi[r.factor-1]!:ℝ)+
      ((k:ℝ)-3-(k:ℝ)*(sumQ p.phi:ℝ)+(k:ℝ)*(p.phi[r.factor-1]!:ℝ))-
      3*(1-(k:ℝ)*(p.phi[r.factor-1]!:ℝ)))/2=
      ((k:ℝ)-6-(k:ℝ)*(sumQ p.phi:ℝ)+6*(k:ℝ)*(p.phi[r.factor-1]!:ℝ))/2 := by ring
  rw [ht]
  simp only [min_assoc]

/-- The basic source is justified by either its four deep caps or the
literal shallow source cap. This is finite rational data, not an estimate. -/
def BasicPhysicalCaps (k : ℕ) (p : Policy) (r : Resource) : Prop :=
  let f := p.phi[r.factor-1]!
  let T := sumQ p.phi
  let b := resourceSizeCap k p r
  0<b ∧ b≤f ∧
    ((b≤q k-6-q k*T+4*q k*f ∧ 4*b≤1-T ∧
      6*b≤q k*(1-T)-(4*q k-1)*f) ∨
      b≤q k-5-q k*T+(q k+2)*f)

def ResourcePhysicalShape (k : ℕ) (p : Policy) (r : Resource) : Prop :=
  match r.kind with
  | .z2 => r.factor=0 ∧ r.order=2
  | .z4 | .z4Refined => r.factor=0 ∧ r.order=4
  | .basic => 0<r.factor ∧ r.factor≤p.phi.size ∧ r.order=2 ∧ BasicPhysicalCaps k p r
  | .refined => 0<r.factor ∧ r.factor≤p.phi.size ∧ 2≤r.order ∧ r.order%2=0
  | .cube => 0<r.factor ∧ r.factor≤p.phi.size ∧ 2≤r.order ∧ r.order%2=0 ∧ p.phi.size=k-2

instance (k : ℕ) (p : Policy) (r : Resource) : Decidable (BasicPhysicalCaps k p r) := by
  unfold BasicPhysicalCaps
  infer_instance
instance (k : ℕ) (p : Policy) (r : Resource) : Decidable (ResourcePhysicalShape k p r) := by
  unfold ResourcePhysicalShape
  split <;> infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_resources8_physical : ∀i : Fin policies8.size,
    ∀j : Fin policies8[i.val].pieces.size,∀r : Fin policies8[i.val].pieces[j.val].resources.size,
    ResourcePhysicalShape 8 policies8[i.val] policies8[i.val].pieces[j.val].resources[r.val] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_resources9_physical : ∀i : Fin policies9.size,
    ∀j : Fin policies9[i.val].pieces.size,∀r : Fin policies9[i.val].pieces[j.val].resources.size,
    ResourcePhysicalShape 9 policies9[i.val] policies9[i.val].pieces[j.val].resources[r.val] := by
  decide +kernel

#print axioms resourceReal_refined
#print axioms resourceReal_cube
#print axioms all_resources8_physical
#print axioms all_resources9_physical
end Waring.PolicyCompletionResourceFormula
