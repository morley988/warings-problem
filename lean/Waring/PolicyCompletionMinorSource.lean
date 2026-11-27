import Waring.PolicyCompletionPolicyPointwise
import Waring.PolicyCompletionMinorGeometry
import Waring.PolicyCompletionRestrictedDilated
import Waring.CertificateTerminalIntegration

/-! # Actual nonauxiliary minor terminals with the literal certified exponent -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace Waring.PolicyCompletionMinorSource
open Certificate SmoothMoments RationalHeight AuxiliaryMajorArcs AuxiliaryMinorHeights
open PolicyCompletionMajorBoxRanges PolicyCompletionMajorIntegral PolicyCompletionMajorPowerRanges
open PolicyCompletionTerminalShape PolicyCompletionShapeCap PolicyCompletionResourceFormula
open PolicyCompletionPolicyPointwise PolicyCompletionMinorGeometry PolicyCompletionMinorRanges
open PolicyCompletionRestrictedDilated CertificateTerminalIntegration SeedCompletionSourceBounds

theorem nonauxiliary_minor_source_bound (k A : ℕ) (p : Policy) (s : Shape)
    (hk : 3≤k) (hA : 0<A) (hdim : p.phi.size+extra s+2=k)
    (hred : Reduction s k p.phi.size A) (D : ℝ) (hD : 1≤D)
    (curve coefficient : Curve) (entry : Entry)
    (hcurve : AdmissibleCurve k curve) (hcoeff : AdmissibleCurve (2*k) coefficient)
    (hheight : PolicyHeightAssociation k curve coefficient p entry.evaluation)
    (hrec : EntryRecurrenceAssociation k curve p entry)
    (hguard : PolicyAnalyticGuards k p) (hchain : PieceChain 0 1 p.pieces.toList)
    (haux : p.auxiliaryOrder=none) (hr : 1≤terminalHalfOrder p)
    (hterminal : MomentAvailable curve (2*terminalHalfOrder p))
    (halloc : ∀i : Fin p.pieces.size,PieceAllocationValid p.phi.size p.pieces[i.val]!)
    (hv : ∀i : Fin p.pieces.size,∀r,ResourcePhysicalShape k p (resourceAt p.pieces[i.val]! r))
    (hav : ∀i : Fin p.pieces.size,∀r,MomentAvailable coefficient (resourceAt p.pieces[i.val]! r).order) :
    SourcePowerBound
      (fun P R=>boxMinorIntegral k (terminalHalfOrder p) (D*P) P R (fun i=>P^(phiReal p i)))
      (terminalMaximum entry.evaluation:ℝ) := by
  let params := terminalParameters k curve p
  let q : ℝ := 1-total (phiReal p)
  let b : ℝ := ((((2*terminalHalfOrder p:ℕ):ℝ)-(k:ℝ))*q)
  let rho : ℝ := ((k*(k-p.phi.size):ℕ):ℝ)+1
  let B : ℝ := boundaryErrorConstant params
  have hB : 0≤B := boundaryErrorConstant_nonneg params
  have hrho : 0<rho := by dsimp [rho]; positivity
  have hk1 : 1≤k := by omega
  have hdim' : p.phi.size<k := by omega
  have hφ := phiReal_pos hguard
  have hshift := phiReal_shift_pos (by omega : 0<k) hguard
  have hq : 0<q := length_pos hdim' (phiReal p) (fun i=>(hshift i).le)
  have hnonaux := nonauxiliary_parameters k curve p s hdim haux
  have hΔ : 0≤((delta k curve (2*terminalHalfOrder p)).getD 0:ℝ) := delta_getD_nonneg hterminal
  have hslope : 0≤(params.slope:ℝ) := by rw [hnonaux.2.1]; positivity
  intro ε hε
  let δ : ℝ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨ηF,CF,PF,hηF,hCF,hPF,hpoint⟩ := policy_piece_source_pointwise k A p s hk hA hdim
    hred D hD hguard coefficient hcoeff halloc hv hav (params.top:ℝ) hrho.le hδ
  obtain ⟨ηg,hηg,CG,hCG,hmean⟩ := even_excess_height_lintegral_dilated hk1 hr hq hD
    (delta_getD_admissible hcurve hterminal) hδ
  obtain ⟨CT,hCT,hintegral⟩ := policy_terminal_integral k curve coefficient p entry
    hheight hrec hguard hchain hslope hδ
  let η₀ : ℝ := min ηF (min ηg (ε/(4*(B*rho+1))))
  have hη₀ : 0<η₀ := lt_min hηF (lt_min hηg (div_pos hε (by positivity)))
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  have hηF' : η≤ηF := hηle.trans (min_le_left _ _)
  have hηg' : η≤ηg := (hηle.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηB : B*(rho*η)≤δ := by
    have hh : η≤ε/(4*(B*rho+1)) := hηle.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hm := (le_div_iff₀ (by positivity : (0:ℝ)<4*(B*rho+1))).mp hh
    dsimp [δ]
    nlinarith
  let c : ℝ := D^k/D
  have hDp : 0<D := zero_lt_one.trans_le hD
  have hc : 0<c := by dsimp [c]; positivity
  let P₀ : ℝ := max PF (c^(1/η))
  refine ⟨CF*CG*CT,by positivity,P₀,(by linarith [hPF,(le_max_left PF (c^(1/η)))]),?_⟩
  intro P hPP
  have hPF' : PF≤P := (le_max_left _ _).trans hPP
  have hP2 : 2≤P := hPF.trans hPF'
  have hP : 1≤P := by linarith
  have hPgt : 1<P := by linarith
  have hPp : 0<P := by linarith
  have hR : 1≤P^η := Real.one_le_rpow hP hη.le
  have hscale : c≤P^η := NormalizedCoefficient.fixed_constant_rpow_bound hc hη ((le_max_right _ _).trans hPP)
  let M : Fin p.phi.size→ℝ := fun i=>P^(phiReal p i)
  let Y : ℝ := boxSmoothLength (D*P) M
  let V : ℝ := P^((k:ℝ)*q)
  let μ := volume.restrict (boxMinorSet k (D*P) (P^η) M)
  let H := height V
  let ell := normalizedHeight P V
  let F : ℝ→ℝ≥0∞ := fun α=>ENNReal.ofReal ‖boxSourceFamily k (D*P) P (P^η) M α‖
  let g : ℝ→ℝ≥0∞ := fun α=>ENNReal.ofReal (‖smoothWeyl k Y (P^η) α‖^(2*terminalHalfOrder p))
  have hY : Y=D*P^q := boxSmoothLength_power hPp D (phiReal p) (fun i=>(hφ i).le)
  have hVp : 0<V := Real.rpow_pos_of_pos hPp _
  have hHmeas : Measurable H := measurable_height hVp
  have hg : Measurable g := ((continuous_smoothWeyl k Y (P^η)).norm.pow _).measurable.ennreal_ofReal
  have hmem : ∀ᵐ α ∂μ, α∈boxMinorSet k (D*P) (P^η) M := ae_restrict_mem (boxMinorSet_measurable k (D*P) (P^η) M)
  have hlo : ∀ᵐ α ∂μ,1≤H α := Filter.Eventually.of_forall (one_le_height V)
  have heq : ∀ᵐ α ∂μ,H α=P^(ell α) :=
    Filter.Eventually.of_forall (fun α=>(height_eq_normalized hPgt V α).symm)
  have hrange : ∀ᵐ α ∂μ,1-rho*η≤ell α ∧ ell α≤(params.top:ℝ) := by
    filter_upwards [hmem] with α hα
    have hh := source_minor_normalized_bounds hk1 hD hPgt hR le_rfl (phiReal p)
      (fun i=>(hφ i).le) hq.le hscale
      (show ¬MajorAtCutoff (D*P) ((boxConductor k (D*P) M/(D*P))*(P^η)^(((k*(k-p.phi.size):ℕ):ℝ))) α by
        simpa only [Real.rpow_natCast] using hα.2)
    refine ⟨hh.1.le,?_⟩
    rw [terminalParameters_top_cast]
    convert hh.2 using 1 <;> ring
  let AF : ℝ := CF*P^(δ-b)
  let KG : ℝ := CG*P^(b+δ)
  have hAF : 0<AF := by dsimp [AF]; positivity
  have hKG : 0<KG := by dsimp [KG]; positivity
  have hp : ∀ᵐ α ∂μ,∀i : Fin p.pieces.size,
      F α≤ENNReal.ofReal AF*ENNReal.ofReal
        (P^((params.base:ℝ)-(params.scale:ℝ)*min 1 (pieceSavingReal k p coefficient p.pieces[i.val]! (ell α)))) := by
    filter_upwards [hmem,hrange] with α hα hrangeα i
    have hℓ0 := normalizedHeight_nonneg hPgt V α
    have hm := source_minor_height_power hk1 hD hPgt hη.le (phiReal p)
      (fun i=>(hφ i).le) hscale hα
    have hb := hpoint P hPF' (P^η) hR
      (Real.rpow_le_rpow_of_exponent_le hP hηF') α (ell α) ⟨hℓ0,hrangeα.2⟩
      (by simpa only [sumQ_cast_eq_total] using hm)
      (by simpa only [sumQ_cast_eq_total] using (height_eq_normalized hPgt V α).le) i
    apply (ENNReal.ofReal_le_ofReal hb).trans_eq
    rw [←ENNReal.ofReal_mul hAF.le]
    congr 1
    rw [hnonaux.1,hnonaux.2.2]
    change CF*P^(amplitude k (phiReal p)+δ-min 1 _/root s)=
      (CF*P^(δ-b))*P^(amplitude k (phiReal p)+b-1/root s*min 1 _)
    rw [mul_assoc,←Real.rpow_add hPp]
    congr 2
    ring
  have hm (Z : ℝ) (hZ : 1≤Z) (_ : Z≤4*P^(params.top:ℝ)) :
      (∫⁻ α in {α|H α≤Z},g α ∂μ)≤ENNReal.ofReal KG*ENNReal.ofReal (Z^(params.slope:ℝ)) := by
    have hsub : μ≤volume.restrict (Set.Ioc 0 1) := Measure.restrict_mono_set volume Set.inter_subset_left
    have hh := hmean P hP Z (P^η) hZ hR (Real.rpow_le_rpow_of_exponent_le hP hηg')
    rw [←hY] at hh
    rw [hnonaux.2.1]
    exact (lintegral_mono' (Measure.restrict_mono_measure hsub _) le_rfl).trans hh
  have hi := hintegral P hP (rho*η) (mul_nonneg hrho.le hη.le) ℝ μ H ell F g
    hHmeas hg hlo heq hrange (ENNReal.ofReal AF) (ENNReal.ofReal KG) hp hm
  change (∫⁻ α,ENNReal.ofReal ‖boxSourceFamily k (D*P) P (P^η) M α‖*
    ENNReal.ofReal (‖smoothWeyl k (boxSmoothLength (D*P) M) (P^η) α‖^(2*terminalHalfOrder p))
      ∂(volume.restrict (boxMinorSet k (D*P) (P^η) M)))≤_ at hi
  rw [←boxMinorIntegral_lintegral] at hi
  have hid : ENNReal.ofReal AF*ENNReal.ofReal KG*
      ENNReal.ofReal (CT*P^((terminalMaximum entry.evaluation:ℝ)+B*(rho*η)+δ))=
      ENNReal.ofReal (CF*CG*CT*P^((terminalMaximum entry.evaluation:ℝ)+B*(rho*η)+3*δ)) := by
    repeat' rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [AF,KG]
    calc
      _ = CF*CG*CT*(P^(δ-b)*P^(b+δ)*P^((terminalMaximum entry.evaluation:ℝ)+B*(rho*η)+δ)) := by ring
      _ = _ := by
        rw [←Real.rpow_add hPp,←Real.rpow_add hPp]
        congr 2
        ring
  rw [hid] at hi
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hi
  change |boxMinorIntegral k (terminalHalfOrder p) (D*P) P (P^η) M|≤_
  have hnon : 0≤boxMinorIntegral k (terminalHalfOrder p) (D*P) P (P^η) M :=
    integral_nonneg (fun α=>mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
  rw [abs_of_nonneg hnon]
  apply hreal.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hP
  dsimp [δ] at hηB ⊢
  linarith

#print axioms nonauxiliary_minor_source_bound
end Waring.PolicyCompletionMinorSource
