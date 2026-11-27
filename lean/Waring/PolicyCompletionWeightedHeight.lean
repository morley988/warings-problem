import Waring.CertificateTerminalIntegration
import Waring.Holder

/-! # Certified height integration after a nonnegative power -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.PolicyCompletionWeightedHeight
open Certificate CertificateTerminalIntegration MinorTerminalIntegration

theorem policy_terminal_integral_rpow
    (k : ℕ) (curve coefficient : Curve) (p : Policy) (entry : Entry)
    (hheight : PolicyHeightAssociation k curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation k curve p entry)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    (hslope : 0≤((terminalParameters k curve p).slope:ℝ))
    {t ε : ℝ} (ht : 0≤t) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀κ : ℝ,0≤κ→
      ∀(α : Type*) [MeasurableSpace α] (μ : Measure α)
        (H ell : α→ℝ) (F g : α→ℝ≥0∞),
      Measurable H→Measurable g→
      (∀ᵐx ∂μ,1≤H x)→(∀ᵐx ∂μ,H x=P^(ell x))→
      (∀ᵐx ∂μ,1-κ≤ell x ∧ ell x≤(terminalParameters k curve p).top)→
      ∀A K : ℝ≥0∞,
      (∀ᵐx ∂μ,∀i : Fin p.pieces.size,
        let params:=terminalParameters k curve p
        F x≤A*ENNReal.ofReal (P^((params.base:ℝ)-(params.scale:ℝ)*
          min 1 (pieceSavingReal k p coefficient p.pieces[i.val]! (ell x)))))→
      (∀Z : ℝ,1≤Z→Z≤4*P^((terminalParameters k curve p).top:ℝ)→
        (∫⁻x in {x|H x≤Z},g x ∂μ)≤K*ENNReal.ofReal (Z^(((terminalParameters k curve p).slope:ℝ)*t)))→
      (∫⁻x,(F x)^t*g x ∂μ)≤A^t*K*ENNReal.ofReal
        (C*P^(((terminalMaximum entry.evaluation:ℝ)+boundaryErrorConstant (terminalParameters k curve p)*κ)*t+ε)) := by
  let params:=terminalParameters k curve p
  have htop : 0<(params.top:ℝ) := by have hh:=hheight.1; exact_mod_cast (show (0:Q)<params.top by linarith)
  obtain ⟨C,hC,hint⟩ := restricted_terminal_from_residual htop (mul_nonneg hslope ht) hε
  refine ⟨C,hC,?_⟩
  intro P hP κ hκ α _ μ H ell F g hH hg hlo heq hrange A K hp hm
  have hPp : 0<P := zero_lt_one.trans_le hP
  let E : ℝ := (terminalMaximum entry.evaluation:ℝ)+boundaryErrorConstant params*κ
  let saving : α→ℝ := fun x=>t*((params.slope:ℝ)*ell x-E)
  have hhi : ∀ᵐx ∂μ,H x≤P^(params.top:ℝ) := by
    filter_upwards [heq,hrange] with x hx hr
    rw [hx]
    exact Real.rpow_le_rpow_of_exponent_le hP hr.2
  have hres : ∀ᵐx ∂μ,((params.slope:ℝ)*t)*ell x-saving x≤E*t :=
    Filter.Eventually.of_forall (fun x=>by dsimp [saving]; nlinarith)
  have hp' : ∀ᵐx ∂μ,(F x)^t≤A^t*ENNReal.ofReal (P^(-saving x)) := by
    filter_upwards [hrange,hp] with x hr hpx
    have hh:=policy_terminal_height_decay k curve coefficient p entry hheight hrec hguard hchain
      hP hκ hr.1 hr.2 (F x) A hpx
    have hh':=ENNReal.rpow_le_rpow hh ht
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht,ENNReal.ofReal_rpow_of_nonneg (by positivity) ht] at hh'
    apply hh'.trans_eq
    congr 1
    congr 1
    rw [←Real.rpow_mul hPp.le,←Real.rpow_add hPp,←Real.rpow_mul hPp.le]
    congr 1
    dsimp [saving,E]
    ring
  exact hint P hP α μ H ell saving (fun x=>(F x)^t) g hH hg hlo hhi heq
    (A^t) K (E*t) hres hp' hm

/-- The source auxiliary split retains its varying pointwise factor inside
one mixed integral. This avoids replacing a restricted family by a larger
family pointwise. -/
theorem auxiliary_global_split {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F g : α→ℝ≥0∞} (hF : AEMeasurable F μ) (hg : AEMeasurable g μ) :
    (∫⁻x,F x*g x^(16:ℕ) ∂μ)≤
      (∫⁻x,F x^(2:ℕ) ∂μ)^(1/5:ℝ)*
      (∫⁻x,F x^(3/4:ℝ)*g x^(20:ℕ) ∂μ)^(4/5:ℝ) := by
  have hh:=ENNReal.lintegral_mul_norm_pow_le
    (hF.pow_const (2:ℝ)) ((hF.pow_const (3/4:ℝ)).mul (hg.pow_const (20:ℝ)))
    (p:=1/5) (q:=4/5) (by norm_num) (by norm_num) (by norm_num)
  have hid (x : α) : (F x^(2:ℝ))^(1/5:ℝ)*(F x^(3/4:ℝ)*g x^(20:ℝ))^(4/5:ℝ)=
      F x*g x^(16:ℕ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤4/5)]
    rw [←ENNReal.rpow_mul,←ENNReal.rpow_mul,←ENNReal.rpow_mul]
    norm_num
    rw [←mul_assoc,←ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  simp_rw [hid] at hh
  simpa only [ENNReal.rpow_ofNat] using hh

#print axioms policy_terminal_integral_rpow
#print axioms auxiliary_global_split
end Waring.PolicyCompletionWeightedHeight
