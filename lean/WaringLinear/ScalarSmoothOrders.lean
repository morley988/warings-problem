import WaringLinear.SelectedGeometricSeed

/-! # Linear orders for the actual rational power-sum integrals on smooth supports -/
noncomputable section
open WaringEnvelope WaringDualEnvelope Waring Waring.SmoothMoments
namespace WaringLinear

def ScalarRootMoment (A : ℝ → ℕ → Finset ℕ) (k r : ℕ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ, 1≤X →
      frequencyEvenMoment (A η X) (fun n => ((n^k:ℕ):ℤ)) (r/2)≤
      C*(X:ℝ)^((r:ℝ)-k+k*x+ε)

theorem scalar_root_moment_of_subset (A : ℝ → ℕ → Finset ℕ) (k r : ℕ) (x : ℝ)
    (smooth : ∀ η : ℝ, 0<η → ∀ X : ℕ, 1≤X → A η X ⊆ smoothNumbers X ((X:ℝ)^η))
    (est : SubsetMoment k r x) : ScalarRootMoment A k r x := by
  classical
  intro ε he
  obtain ⟨v,hv,C,hC,P₀,hP,global⟩ := est ε he
  refine ⟨v,hv,?_⟩
  intro η hη hηv
  let e : ℝ := (r:ℝ)-k+k*x+ε
  let E (n : ℕ) : ℝ := frequencyEvenMoment (A η n) (fun n => ((n^k:ℕ):ℤ)) (r/2)
  let T (n : ℕ) : ℝ := |E n / (n:ℝ)^e|
  let B := ∑ n∈Finset.Icc 1 ⌈P₀⌉₊, T n
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C+B,by linarith,?_⟩
  intro X hX
  have hX' : (1:ℝ)≤X := by exact_mod_cast hX
  have hpow : 0<(X:ℝ)^e := Real.rpow_pos_of_pos (zero_lt_one.trans_le hX') _
  change E X≤(C+B)*(X:ℝ)^e
  by_cases h : P₀≤X
  · have hh := global X h ((X:ℝ)^η) (Real.one_le_rpow hX' hη.le)
      (Real.rpow_le_rpow_of_exponent_le hX' hηv) (A η X) (smooth η hη X hX)
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : C≤C+B) hpow.le)
  · have hsmall : X≤⌈P₀⌉₊ := by exact_mod_cast (le_of_not_ge h).trans (Nat.le_ceil P₀)
    have hx := Finset.single_le_sum (s:=Finset.Icc 1 ⌈P₀⌉₊) (f:=T)
      (fun n _ => abs_nonneg _) (Finset.mem_Icc.mpr ⟨hX,hsmall⟩)
    have hh : E X/(X:ℝ)^e ≤ B := (le_abs_self _).trans hx
    exact ((div_le_iff₀ hpow).1 hh).trans (mul_le_mul_of_nonneg_right
      (by linarith : B≤C+B) hpow.le)

/-- The starting mean value is unconditional for each positive integer
smooth support. The remaining input is the actual conductor shortening
for this family of Fourier moments. -/
theorem scalar_linear_orders_from_smooth_seed (A : ℝ → ℕ → Finset ℕ) (k : ℕ) (hk : 21≤k)
    (smooth : ∀ η : ℝ, 0<η → ∀ X : ℕ, 1≤X → A η X ⊆ smoothNumbers X ((X:ℝ)^η))
    (finiteStep : k<180000^2 → ShorteningStep DualStage (ScalarRootMoment A k) k)
    (largeStep : 180000^2≤k → ShorteningStep WaringSharpTail.Branch (ScalarRootMoment A k) k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ ScalarRootMoment A k r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)<(8183:ℝ)/1000*k+6 :=
  selected_geometric_orders k hk _ (fun r x => scalar_root_moment_of_subset A k r x smooth)
    finiteStep largeStep

#print axioms scalar_root_moment_of_subset
#print axioms scalar_linear_orders_from_smooth_seed
end WaringLinear
