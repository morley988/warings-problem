import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact continuous conductor intervals for successive differences

A branch records a legal real shift at each differencing step. Its final
interval is the square-root completion interval for the residual conductor.
-/
noncomputable section
namespace WaringEnvelope

inductive DifferencingBranch (θ : ℝ) : ℕ → ℝ → ℝ → Prop
  | completion (u σ : ℝ) (hl : 2*σ≤u) (hu : u≤2-2*σ) :
      DifferencingBranch θ 0 u σ
  | shift {j : ℕ} {u σ : ℝ} (a : ℝ) (hθ : θ≤a) (hau : a≤u)
      (hdiag : 2*σ≤1-a) (residual : DifferencingBranch θ j (u-a) (2*σ)) :
      DifferencingBranch θ (j+1) u σ

def diffLower (j : ℕ) (θ σ : ℝ) : ℝ := j*θ+2*2^j*σ

def diffUpper (j : ℕ) (σ : ℝ) : ℝ := j+2-(4*2^j-2)*σ

private theorem diff_interval_and_reach (j : ℕ) (θ σ : ℝ)
    (ht : 0≤θ) (hs : 0≤σ) (hbase : 2*((2:ℝ)^j*σ)≤1)
    (hshift : j=0 ∨ θ≤1-(2:ℝ)^j*σ) :
    diffLower j θ σ ≤ diffUpper j σ ∧
      ∀ u, diffLower j θ σ ≤ u → u ≤ diffUpper j σ → DifferencingBranch θ j u σ := by
  induction j generalizing σ with
  | zero =>
    simp only [diffLower,diffUpper,Nat.cast_zero,pow_zero,zero_mul,zero_add,mul_one,one_mul] at *
    refine ⟨by linarith,?_⟩
    intro u hlow hupp
    apply DifferencingBranch.completion <;> linarith
  | succ j ih =>
    have ht' : θ≤1-(2:ℝ)^j*(2*σ) := by
      rcases hshift with hf|hf
      · omega
      · rw [pow_succ] at hf
        linarith
    have hib : 2*((2:ℝ)^j*(2*σ))≤1 := by rw [pow_succ] at hbase; linarith
    obtain ⟨hprev,reach⟩ := ih (2*σ) (by positivity) hib (Or.inr ht')
    have ht2 : θ≤1-2*σ := by
      have h1 : (1:ℝ)≤2^j := one_le_pow₀ (by norm_num)
      have h2 := mul_le_mul_of_nonneg_right h1 (show 0≤2*σ by positivity)
      linarith
    have hlo : diffLower (j+1) θ σ = θ+diffLower j θ (2*σ) := by
      simp only [diffLower,Nat.cast_succ,pow_succ]; ring
    have hup : diffUpper (j+1) σ = (1-2*σ)+diffUpper j (2*σ) := by
      simp only [diffUpper,Nat.cast_succ,pow_succ]; ring
    rw [hlo,hup]
    refine ⟨add_le_add ht2 hprev,?_⟩
    intro u hlu hhu
    let a := max θ (u-diffUpper j (2*σ))
    have ha : θ≤a := le_max_left _ _
    have hdiag : a≤1-2*σ := max_le ht2 (by linarith)
    have hal : a ≤ u-diffLower j θ (2*σ) := max_le (by linarith) (by linarith)
    have hau : u-diffUpper j (2*σ) ≤ a := le_max_right _ _
    have hpos : 0≤diffLower j θ (2*σ) := by unfold diffLower; positivity
    exact .shift a ha (by linarith) (by linarith) (reach _ (by linarith) (by linarith))

/-- Continuous interpretation of every dyadic differencing cell. -/
theorem interval_has_differencing_branch (j : ℕ) (θ σ u : ℝ) (ht : 0≤θ) (hs : 0≤σ)
    (hbase : 2*((2:ℝ)^j*σ)≤1) (hshift : j=0 ∨ θ≤1-(2:ℝ)^j*σ)
    (hl : diffLower j θ σ≤u) (hu : u≤diffUpper j σ) : DifferencingBranch θ j u σ :=
  (diff_interval_and_reach j θ σ ht hs hbase hshift).2 u hl hu

#print axioms interval_has_differencing_branch
end WaringEnvelope
