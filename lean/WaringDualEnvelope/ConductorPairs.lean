import WaringDualEnvelope.Check
import WaringEnvelope.RealCosts

/-! # Real saving certified by an arithmetic exponent-pair cell -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope

def kappa (p : Pair) : ℝ := (p.x:ℝ)/p.denominator
def lambda (p : Pair) : ℝ := (p.y:ℝ)/p.denominator
def radical (p : Pair) : ℝ := (p.loss:ℝ)/p.lossDen

private theorem pairCleared_sound (p : Pair) (h v m sig : Nat)
    (hd : 0<p.denominator) (hl : 0<p.lossDen) (hv : 0<v)
    (hc : sig*p.denominator*B*p.lossDen*v + T*(p.y*B*p.lossDen*v +
      p.x*m*p.lossDen*v+(p.loss+p.lossDen)*p.denominator*B*h) ≤
      T*(p.denominator+p.x)*B*p.lossDen*v)
    (u θ : ℝ) (hu : u≤(m:ℝ)/B) (ht : θ≤(h:ℝ)/v) :
    (sig:ℝ)/T ≤ 1-lambda p+kappa p-kappa p*u-(1+radical p)*θ := by
  have hD : (0:ℝ)<p.denominator := by exact_mod_cast hd
  have hL : (0:ℝ)<p.lossDen := by exact_mod_cast hl
  have hV : (0:ℝ)<v := by exact_mod_cast hv
  have hB : (0:ℝ)<B := by norm_num [B]
  have hT : (0:ℝ)<T := by norm_num [T]
  have hh : (sig:ℝ)*p.denominator*B*p.lossDen*v + T*(p.y*B*p.lossDen*v +
      p.x*m*p.lossDen*v+(p.loss+p.lossDen)*p.denominator*B*h) ≤
      T*(p.denominator+p.x)*B*p.lossDen*v := by exact_mod_cast hc
  have hp : (sig:ℝ)/T ≤ 1-lambda p+kappa p-kappa p*((m:ℝ)/B)-(1+radical p)*((h:ℝ)/v) := by
    unfold kappa lambda radical
    field_simp
    linarith only [hh]
  have hk : 0≤kappa p := by unfold kappa; positivity
  have hr : 0≤1+radical p := by unfold radical; positivity
  have hu' := mul_le_mul_of_nonneg_left hu hk
  have ht' := mul_le_mul_of_nonneg_left ht hr
  linarith

/-- The right-endpoint test proves the claimed saving simultaneously at all
smaller conductor and radical parameters used in the cell. -/
theorem pairAdmits_sound (c : Config) (p : Pair) (m sig : Nat)
    (h : pairAdmits c m sig p = true) (u θ : ℝ) (hu : u≤(m:ℝ)/B)
    (ht : θ ≤ (if c.last=0 then 1/((8:ℝ)*c.root) else (m:ℝ)/(B*c.first))) :
    (sig:ℝ)/T ≤ 1-lambda p+kappa p-kappa p*u-(1+radical p)*θ := by
  by_cases hz : c.last=0
  · simp only [pairAdmits,hz,if_true,Bool.and_eq_true,decide_eq_true_eq] at h
    simp only [hz,if_true] at ht
    apply pairCleared_sound p 1 (8*c.root) m sig h.1.1.1 h.1.1.2 h.1.2 h.2 u θ hu
    simpa using ht
  · simp only [pairAdmits,hz,if_false,Bool.and_eq_true,decide_eq_true_eq] at h
    simp only [hz,if_false] at ht
    apply pairCleared_sound p m (B*c.first) m sig h.1.1.1 h.1.1.2 h.1.2 h.2 u θ hu
    simpa using ht

#print axioms pairAdmits_sound
end WaringDualEnvelope
