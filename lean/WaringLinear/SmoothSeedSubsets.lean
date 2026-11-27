import WaringLinear.SmoothSeed
import Waring.EvenMoments
import Waring.SmoothMomentGrowth
import WaringEnvelope.FiniteOrder
import WaringEnvelope.LogBounds

/-! # The unconditional initial bound for arbitrary smooth subfamilies -/
noncomputable section
namespace WaringLinear
open Waring Waring.SmoothMoments WaringEnvelope

/-- A defect bound applies simultaneously to every subset of the smooth
roots. The cutoff depends on the requested accuracy. -/
def SubsetMoment (k r : ℕ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ η : ℝ, 0<η ∧ ∃ C : ℝ, 0<C ∧ ∃ P₀ : ℝ, 1≤P₀ ∧
    ∀ P : ℝ, P₀≤P → ∀ R : ℝ, 1≤R → R≤P^η →
    ∀ A : Finset ℕ, A⊆smoothNumbers P R →
    Waring.frequencyEvenMoment A (fun n => ((n^k:ℕ):ℤ)) (r/2) ≤
      C*P^((r:ℝ)-k+k*x+ε)

theorem subset_moment_of_smooth {k r : ℕ} {x : ℝ} (er : Even r)
    (he : AdmissibleExcess k r ((k:ℝ)*x)) : SubsetMoment k r x := by
  obtain ⟨s,hs⟩ := er
  have h : r=2*s := by omega
  intro ε hε
  obtain ⟨η,hη,C,hC,P₀,hP,major⟩ := he ε hε
  refine ⟨η,hη,C,hC,P₀,hP,?_⟩
  intro P hp R hR hm A hA
  have hb := major P hp R hR hm
  rw [h,smoothMoment_even_eq_frequency] at hb
  rw [h,show 2*s/2=s by omega]
  exact (frequencyEvenMoment_mono hA _ _).trans hb

/-- On the height range used by the scalar certificate, the difference
between the two starting prices is at most two per degree. -/
theorem geometric_seed_allowance (z : ℕ) (hlo : T≤20*z) (hhi : 3*z≤T) :
    -(2:ℝ)*Real.log (seedDefect z) ≤ seedOrder z+2 := by
  obtain ⟨hz,hu,_,hD,_⟩ := seed_range z hlo (by omega)
  have hpos : 0<1-normalizedHeight z := by linarith
  have hlow : 1/19≤seedDefect z := (le_div_iff₀ hpos).2 (by linarith only [hz])
  have hd : 0<seedDefect z := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0:ℝ)<1/19) hd)
  rw [Real.log_div (by norm_num) hd.ne',Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hlog
  have hfrac : 1/19/(seedDefect z)≤1+1/19-seedDefect z := by
    apply (div_le_iff₀ hd).2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hD)]
  have hnum := validLog_sound 19 1 (2946*D/1000) (by decide +kernel)
  norm_num [D] at hnum
  unfold seedOrder
  linarith only [hlog,hfrac,hnum]

def seedShift (k : ℕ) := 2*k+4

theorem shifted_subset_seed (k z : ℕ) (hk : 2≤k) (hlo : T≤20*z) (hhi : 3*z≤T) :
    SubsetMoment k (evenOrder (k*seedOrder z)+seedShift k) (seedDefect z) := by
  obtain ⟨hz,_,h₀,_,hv⟩ := seed_range z hlo (by omega)
  have hd : 0<seedDefect z := by linarith only [hz,h₀]
  have hs := geometric_smooth_seed k (seedDefect z) hk hd
  have hscale := mul_le_mul_of_nonneg_left (geometric_seed_allowance z hlo hhi) (Nat.cast_nonneg (α:=ℝ) k)
  have hceil := Nat.ceil_le_ceil (show -(k:ℝ)*Real.log (seedDefect z)≤(k:ℝ)*seedOrder z/2+k by linarith only [hscale])
  rw [Nat.ceil_add_natCast (by positivity : 0≤(k:ℝ)*seedOrder z/2)] at hceil
  have horder : 2*(⌈-(k:ℝ)*Real.log (seedDefect z)⌉₊+2)≤evenOrder (k*seedOrder z)+seedShift k := by
    unfold evenOrder seedShift
    omega
  apply subset_moment_of_smooth _ (admissibleExcess_order_growth hs horder)
  unfold evenOrder seedShift
  exact ⟨⌈(k:ℝ)*seedOrder z/2⌉₊+k+2,by omega⟩

#print axioms subset_moment_of_smooth
#print axioms shifted_subset_seed
end WaringLinear
