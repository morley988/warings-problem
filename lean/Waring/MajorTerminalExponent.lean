import Waring.SublevelIntegration
import Waring.DyadicLogLoss

/-!
# The auxiliary major-terminal exponent with a uniform epsilon loss

Actual restricted means are combined with actual pointwise height decay.
The dyadic cover and its logarithmic loss are discharged. The remaining
premises are the source estimates themselves, not a terminal-exponent claim.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace Waring.MajorTerminalExponent
open Waring.SublevelIntegration

theorem efficient_dyadic_cover {P : ℝ} (hP : 1 ≤ P) :
    ∃ T : ℕ, P ≤ (2:ℝ)^T ∧ (2:ℝ)^T ≤ 4*P := by
  let N := ⌈P⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (zero_lt_one.trans_le hP)
  have hPN : P ≤ (N:ℝ) := Nat.le_ceil P
  have hNP : (N:ℝ) ≤ 2*P := by
    have hh := (Nat.ceil_lt_add_one (zero_le_one.trans hP)).le
    dsimp [N]
    linarith
  refine ⟨Nat.clog 2 N,?_,?_⟩
  · exact hPN.trans (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) N)
  · exact (DyadicLogLoss.pow_clog_le_twice N hN).trans (by linarith)

theorem dyadic_max_power {P : ℝ} {T : ℕ} (hP : 1 ≤ P)
    (hT : (2:ℝ)^T ≤ 4*P) (e : ℝ) :
    max 1 (((2:ℝ)^T)^e) ≤ (4:ℝ)^(max 0 e)*P^(max 0 e) := by
  have hP0 := zero_le_one.trans hP
  have hbase : 1 ≤ (2:ℝ)^T := one_le_pow₀ (by norm_num)
  by_cases he : 0 ≤ e
  · rw [max_eq_right he, max_eq_right (Real.one_le_rpow hbase he)]
    calc
      _ ≤ (4*P)^e := Real.rpow_le_rpow (by positivity) hT he
      _ = _ := Real.mul_rpow (by norm_num) hP0
  · rw [max_eq_left (le_of_not_ge he), max_eq_left
      (Real.rpow_le_one_of_one_le_of_nonpos hbase (le_of_not_ge he))]
    simp

theorem dyadic_terminal_epsilon {θ lam ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ T : ℕ,
      (2:ℝ)^T ≤ 4*P →
      (2:ℝ)^θ*(T+1:ℕ)*max 1 (((2:ℝ)^T)^(lam-θ)) ≤
        C*P^(max 0 (lam-θ)+ε) := by
  obtain ⟨D,hD,hdepth⟩ := DyadicLogLoss.dyadic_depth_pow_le_rpow 1 hε
  let e := max 0 (lam-θ)
  refine ⟨(2:ℝ)^θ*D*(2:ℝ)^ε*(4:ℝ)^e,by positivity,?_⟩
  intro P hP T hT
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hdep : ((T+1:ℕ):ℝ) ≤ D*(2*P)^ε := by
    have hh := hdepth (2*P) (by linarith) T (by linarith)
    simpa only [pow_one] using hh
  have hm := dyadic_max_power hP hT (lam-θ)
  calc
    _ ≤ (2:ℝ)^θ*(D*(2*P)^ε)*((4:ℝ)^e*P^e) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hPp.le, Real.rpow_add hPp]
      dsimp [e]
      ring

/-- The major terminal's max(0,lambda-theta) follows from source restricted
means, uniformly with every finite constant and epsilon choice displayed. -/
theorem restricted_major_epsilon {θ lam ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α)
        (H : α → ℝ) (F g : α → ℝ≥0∞),
      Measurable H → Measurable g →
      (∀ᵐ x ∂μ, 1 ≤ H x) → (∀ᵐ x ∂μ, H x ≤ P) →
      ∀ A K : ℝ≥0∞,
      (∀ᵐ x ∂μ, F x ≤ A*ENNReal.ofReal ((H x)^(-θ))) →
      (∀ Z : ℝ, 1 ≤ Z → Z ≤ 4*P →
        (∫⁻ x in {x | H x ≤ Z}, g x ∂μ) ≤ K*ENNReal.ofReal (Z^lam)) →
      (∫⁻ x, F x*g x ∂μ) ≤ A*K*ENNReal.ofReal (C*P^(max 0 (lam-θ)+ε)) := by
  obtain ⟨C,hC,hbound⟩ := dyadic_terminal_epsilon (θ:=θ) (lam:=lam) hε
  refine ⟨C,hC,?_⟩
  intro P hP α _ μ H F g hH hg hlo hhi A K hpoint hmeans
  obtain ⟨T,hPT,hTP⟩ := efficient_dyadic_cover hP
  have hupper : ∀ᵐ x ∂μ, H x ≤ (2:ℝ)^T := hhi.mono (fun x hx => hx.trans hPT)
  have hdyadic (j : ℕ) (hj : j ∈ Finset.range (T+1)) :
      (∫⁻ x in {x | H x ≤ (2:ℝ)^j}, g x ∂μ) ≤ K*ENNReal.ofReal (((2:ℝ)^j)^lam) := by
    apply hmeans _ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    apply le_trans _ hTP
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
      (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj)
  apply (restricted_mean_majorant_integral H F g T hH hg hθ hlo hupper A K hpoint hdyadic).trans
  exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal (hbound P hP T hTP)) (A*K)

/-- The source's approximation error A*P^-theta is retained. Its integral
has the same max(0,lambda-theta) exponent; no error term is discarded. -/
theorem restricted_major_with_error_epsilon {θ lam ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α)
        (H : α → ℝ) (F g : α → ℝ≥0∞),
      Measurable H → Measurable g →
      (∀ᵐ x ∂μ, 1 ≤ H x) → (∀ᵐ x ∂μ, H x ≤ P) →
      ∀ A K : ℝ≥0∞,
      (∀ᵐ x ∂μ, F x ≤ A*(ENNReal.ofReal ((H x)^(-θ))+ENNReal.ofReal (P^(-θ)))) →
      (∀ Z : ℝ, 1 ≤ Z → Z ≤ 4*P →
        (∫⁻ x in {x | H x ≤ Z}, g x ∂μ) ≤ K*ENNReal.ofReal (Z^lam)) →
      (∫⁻ x, F x*g x ∂μ) ≤ A*K*ENNReal.ofReal (C*P^(max 0 (lam-θ)+ε)) := by
  obtain ⟨C,hC,hbound⟩ := restricted_major_epsilon (lam:=lam) hθ hε
  refine ⟨C+1,by positivity,?_⟩
  intro P hP α _ μ H F g hH hg hlo hhi A K hpoint hmeans
  let E := max 0 (lam-θ)+ε
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hweight : Measurable (fun x => A*ENNReal.ofReal ((H x)^(-θ))*g x) :=
    (measurable_const.mul (hH.pow_const _).ennreal_ofReal).mul hg
  have herror : Measurable (fun x : α => (A*ENNReal.ofReal (P^(-θ)))*g x) :=
    measurable_const.mul hg
  have hmain := hbound P hP α μ H (fun x => A*ENNReal.ofReal ((H x)^(-θ))) g
    hH hg hlo hhi A K (Filter.Eventually.of_forall (fun x => le_rfl)) hmeans
  have hfull : (∫⁻ x, g x ∂μ) ≤ K*ENNReal.ofReal (P^lam) := by
    have hh := hmeans P hP (by linarith)
    have hres : μ.restrict {x | H x ≤ P} = μ :=
      Measure.restrict_eq_self_of_ae_mem (s := {x | H x ≤ P}) hhi
    simpa only [hres] using hh
  have hpowers : P^(-θ)*P^lam ≤ P^E := by
    rw [← Real.rpow_add hPp]
    apply Real.rpow_le_rpow_of_exponent_le hP
    dsimp [E]
    have hh := le_max_right (0:ℝ) (lam-θ)
    linarith
  have herr : (∫⁻ x, (A*ENNReal.ofReal (P^(-θ)))*g x ∂μ) ≤ A*K*ENNReal.ofReal (P^E) := by
    rw [lintegral_const_mul _ hg]
    calc
      _ ≤ (A*ENNReal.ofReal (P^(-θ)))*(K*ENNReal.ofReal (P^lam)) := mul_le_mul_left' hfull _
      _ = A*K*ENNReal.ofReal (P^(-θ)*P^lam) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hPp.le _)]
        ac_rfl
      _ ≤ _ := mul_le_mul_left' (ENNReal.ofReal_le_ofReal hpowers) _
  calc
    _ ≤ ∫⁻ x, A*ENNReal.ofReal ((H x)^(-θ))*g x+
        (A*ENNReal.ofReal (P^(-θ)))*g x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with x hx
      simpa only [mul_add,add_mul,mul_assoc] using mul_le_mul_right' hx (g x)
    _ = (∫⁻ x, A*ENNReal.ofReal ((H x)^(-θ))*g x ∂μ)+
        (∫⁻ x, (A*ENNReal.ofReal (P^(-θ)))*g x ∂μ) :=
      lintegral_add_left hweight _
    _ ≤ A*K*ENNReal.ofReal (C*P^E)+A*K*ENNReal.ofReal (P^E) := add_le_add hmain herr
    _ = A*K*ENNReal.ofReal ((C+1)*P^E) := by
      rw [← mul_add,← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      ring

#print axioms restricted_major_epsilon
#print axioms restricted_major_with_error_epsilon

end Waring.MajorTerminalExponent
