import Waring.MinorTerminalIntegration
import Waring.CertificateBoundaryRecurrence

/-!
# Literal certificate pieces control an actual terminal integral

The analytic resource estimates remain explicit pointwise premises. This
module selects a certified piece at each actual height, including the lower
boundary displacement, and proves the resulting integral using an explicit
restricted-mean premise. The endpoint maximum and all resource formulas come
from the original checked entry.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.CertificateTerminalIntegration
open Certificate MinorTerminalIntegration MajorTerminalExponent

theorem policy_terminal_height_decay
    (k : Nat) (curve coefficient : Curve) (p : Policy) (entry : Entry)
    (hheight : PolicyHeightAssociation k curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation k curve p entry)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    {P ell κ : ℝ} (hP : 1 ≤ P) (hκ : 0 ≤ κ) (hlo : 1-κ ≤ ell)
    (hhi : ell ≤ (terminalParameters k curve p).top)
    (F A : ℝ≥0∞)
    (hpoint : ∀ i : Fin p.pieces.size,
      let params := terminalParameters k curve p
      F ≤ A*ENNReal.ofReal (P^((params.base : ℝ)-(params.scale : ℝ)*
        min 1 (pieceSavingReal k p coefficient p.pieces[i.val]! ell)))) :
    let params := terminalParameters k curve p
    F ≤ A*ENNReal.ofReal
      (P^((terminalMaximum entry.evaluation : ℝ)+boundaryErrorConstant params*κ)*
        (P^ell)^(-(params.slope : ℝ))) := by
  obtain ⟨i,hi⟩ := policyHeightAssociation_extended k curve coefficient p entry.evaluation
    hheight hguard hchain ell κ hκ hlo hhi
  let params := terminalParameters k curve p
  have hend : max (entry.evaluation.pieces[i.val]!.endpoints[0]!.exponent : ℝ)
      (entry.evaluation.pieces[i.val]!.endpoints[1]!.exponent : ℝ) ≤
      (terminalMaximum entry.evaluation : ℝ) := by
    rw [← cast_qmax]
    exact_mod_cast hrec.2.2.1 i
  have hres := hi.trans (add_le_add_right hend (boundaryErrorConstant params*κ))
  exact (hpoint i).trans (mul_le_mul_left'
    (ENNReal.ofReal_le_ofReal (certificate_residual_to_height_decay k p coefficient
      p.pieces[i.val]! params.base params.slope params.scale hP hres)) A)

/-- A real integral version of the literal checked terminal. The source
restricted means and actual per-piece exponential-sum estimates are explicit.
The continuum of heights, piece selection, boundary correction, dyadic sum
and epsilon loss have all been discharged. -/
theorem policy_terminal_integral
    (k : Nat) (curve coefficient : Curve) (p : Policy) (entry : Entry)
    (hheight : PolicyHeightAssociation k curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation k curve p entry)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    (hslope : 0 ≤ ((terminalParameters k curve p).slope : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ κ : ℝ, 0 ≤ κ →
      ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α)
        (H ell : α → ℝ) (F g : α → ℝ≥0∞),
      Measurable H → Measurable g →
      (∀ᵐ x ∂μ, 1 ≤ H x) →
      (∀ᵐ x ∂μ, H x = P^(ell x)) →
      (∀ᵐ x ∂μ, 1-κ ≤ ell x ∧ ell x ≤ (terminalParameters k curve p).top) →
      ∀ A K : ℝ≥0∞,
      (∀ᵐ x ∂μ, ∀ i : Fin p.pieces.size,
        let params := terminalParameters k curve p
        F x ≤ A*ENNReal.ofReal (P^((params.base : ℝ)-(params.scale : ℝ)*
          min 1 (pieceSavingReal k p coefficient p.pieces[i.val]! (ell x))))) →
      (∀ Z : ℝ, 1 ≤ Z → Z ≤ 4*P^((terminalParameters k curve p).top : ℝ) →
        (∫⁻ x in {x | H x ≤ Z}, g x ∂μ) ≤
          K*ENNReal.ofReal (Z^((terminalParameters k curve p).slope : ℝ))) →
      (∫⁻ x, F x*g x ∂μ) ≤ A*K*ENNReal.ofReal
        (C*P^((terminalMaximum entry.evaluation : ℝ)+
          boundaryErrorConstant (terminalParameters k curve p)*κ+ε)) := by
  let params := terminalParameters k curve p
  have htop : 1 ≤ (params.top : ℝ) := by exact_mod_cast hheight.1
  have htoppos : 0 < (params.top : ℝ) := zero_lt_one.trans_le htop
  obtain ⟨C,hC,hterminal⟩ := restricted_terminal_from_residual htoppos hslope hε
  refine ⟨C,hC,?_⟩
  intro P hP κ hκ α _ μ H ell F g hH hg hlo heq hrange A K hpoint hmeans
  let E : ℝ := (terminalMaximum entry.evaluation : ℝ)+boundaryErrorConstant params*κ
  let saving : α → ℝ := fun x => (params.slope : ℝ)*ell x-E
  have hupper : ∀ᵐ x ∂μ, H x ≤ P^(params.top : ℝ) := by
    filter_upwards [heq,hrange] with x hx hr
    rw [hx]
    exact Real.rpow_le_rpow_of_exponent_le hP hr.2
  have hres : ∀ᵐ x ∂μ, (params.slope : ℝ)*ell x-saving x ≤ E :=
    Filter.Eventually.of_forall (fun x => by dsimp [saving]; linarith)
  have hp : ∀ᵐ x ∂μ, F x ≤ A*ENNReal.ofReal (P^(-saving x)) := by
    filter_upwards [hrange,hpoint] with x hr hp
    have hh := policy_terminal_height_decay k curve coefficient p entry hheight hrec hguard hchain
      hP hκ hr.1 hr.2 (F x) A hp
    have hid : P^E*(P^(ell x))^(-(params.slope : ℝ)) = P^(-saving x) := by
      rw [← Real.rpow_mul (zero_le_one.trans hP),
        ← Real.rpow_add (zero_lt_one.trans_le hP)]
      congr 1
      dsimp [saving]
      ring
    exact hid ▸ hh
  exact hterminal P hP α μ H ell saving F g hH hg hlo hupper heq A K E hres hp hmeans

#print axioms policy_terminal_height_decay
#print axioms policy_terminal_integral
end Waring.CertificateTerminalIntegration
