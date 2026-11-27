import WaringSiegel.LargeKArithmetic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Strict numerical margins in Ramanujam's local summand counts

These are arithmetic estimates only. They do not assert that a local
power representation with the indicated count has been constructed.
The small-residue estimate deliberately permits the full interpolation
degree, and uses only the elementary residue-degree bound f<=m-1.
-/
namespace WaringSiegel.WSL4Local

theorem ramanujam_large_residue_count_lt (m : ℝ) (hm : 2≤m) :
    (m^2+m+1)*(4*m+1)<8*m^5 := by
  let t := m-2
  have ht : 0≤t := by dsimp [t]; linarith
  have hidentity : 8*m^5-(m^2+m+1)*(4*m+1)=
      8*t^5+80*t^4+316*t^3+611*t^2+567*t+193 := by dsimp [t]; ring
  have hpos : 0<8*t^5+80*t^4+316*t^3+611*t^2+567*t+193 := by positivity
  linarith

theorem ramanujam_small_residue_envelope_lt (m : ℝ) (hm : 3≤m) :
    (4*m+1)/2*m*(m+1)^2*(2*m-1)+
      (m-1)*(4*m-1)*(m^2+m*(m+1)/2+1)<8*m^5 := by
  let t := m-3
  have ht : 0≤t := by dsimp [t]; linarith
  have hidentity : 8*m^5-
      ((4*m+1)/2*m*(m+1)^2*(2*m-1)+
        (m-1)*(4*m-1)*(m^2+m*(m+1)/2+1))=
      4*t^5+47*t^4+208*t^3+413*t^2+323*t+32 := by dsimp [t]; ring
  have hpos : 0<4*t^5+47*t^4+208*t^3+413*t^2+323*t+32 := by positivity
  linarith

/-- Numerical conclusion from the actual two terms in the local count.
Here d is q1-1 in the filtered construction, or 1 in full interpolation. -/
theorem ramanujam_small_residue_count_lt
    (m P n d c N f A T : ℝ) (hm : 3≤m)
    (hP : 0≤P) (hn : 0≤n) (hd : 0≤d) (hc : 0≤c)
    (hN : 0≤N) (hf : 0≤f) (hA : 0≤A) (hT : 0≤T)
    (hnP : n*P=m) (hPm : P≤m) (hdc : d*c≤P) (hcm : c≤m)
    (hNm : N≤4*m+1) (hfm : f≤m-1) (hAm : A≤2*m-1) (hTm : T≤4*m-1) :
    N/2*d*c*(c+1)^2*A+f*T*(c*m+n*d*c*(c+1)/2+1)<8*m^5 := by
  have hm0 : 0≤m := by linarith
  have hm1 : 0≤m-1 := by linarith
  have hm4 : 0≤4*m-1 := by linarith
  have hdc0 : 0≤d*c := mul_nonneg hd hc
  have hdcm : d*c≤m := hdc.trans hPm
  have hndc : n*(d*c)≤m := by
    simpa only [hnP] using mul_le_mul_of_nonneg_left hdc hn
  have hfirst : N/2*d*c*(c+1)^2*A≤(4*m+1)/2*m*(m+1)^2*(2*m-1) := by
    calc
      N/2*d*c*(c+1)^2*A=(N/2)*(d*c)*(c+1)^2*A := by ring
      _≤(4*m+1)/2*m*(m+1)^2*(2*m-1) := by gcongr
  have hbody : c*m+n*d*c*(c+1)/2+1≤m^2+m*(m+1)/2+1 := by
    have h1 : c*m≤m*m := mul_le_mul_of_nonneg_right hcm hm0
    have h2 : n*d*c*(c+1)≤m*(m+1) := by
      calc
        n*d*c*(c+1)=(n*(d*c))*(c+1) := by ring
        _≤m*(m+1) := by gcongr
    nlinarith
  have hsecond : f*T*(c*m+n*d*c*(c+1)/2+1)≤
      (m-1)*(4*m-1)*(m^2+m*(m+1)/2+1) := by gcongr
  exact (add_le_add hfirst hsecond).trans_lt (ramanujam_small_residue_envelope_lt m hm)

#print axioms ramanujam_large_residue_count_lt
#print axioms ramanujam_small_residue_count_lt
end WaringSiegel.WSL4Local
