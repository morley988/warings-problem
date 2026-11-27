import Waring.PolicyCompletionMinorSource
import Waring.PolicyCompletionWeightedHeight
import Waring.PolicyCompletionAuxiliaryParameters
import Waring.PolicyCompletionAuxiliaryScalar

/-! # The actual auxiliary degree-eight minor terminal with its frozen weights -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace Waring.PolicyCompletionAuxiliaryMinor
open Certificate SmoothMoments RationalHeight AuxiliaryMajorArcs AuxiliaryMinorHeights
open PolicyCompletionMajorBoxRanges PolicyCompletionMajorIntegral PolicyCompletionMajorPowerRanges
open PolicyCompletionTerminalShape PolicyCompletionShapeCap PolicyCompletionResourceFormula
open PolicyCompletionPolicyPointwise PolicyCompletionMinorGeometry PolicyCompletionMinorRanges
open PolicyCompletionRestrictedDilated SeedCompletionSourceBounds PolicyCompletionWeightedHeight
open PolicyCompletionAuxiliarySource PolicyCompletionAuxiliaryParameters PolicyCompletionAuxiliaryScalar

set_option maxHeartbeats 800000 in
theorem auxiliary_minor_source_bound (curve coefficient : Curve) (entry : Entry)
    (hcurve : AdmissibleCurve 8 curve) (hcoeff : AdmissibleCurve 16 coefficient)
    (hheight : PolicyHeightAssociation 8 curve coefficient policies8[0]! entry.evaluation)
    (hrec : EntryRecurrenceAssociation 8 curve policies8[0]! entry)
    (hguard : PolicyAnalyticGuards 8 policies8[0]!)
    (hchain : PieceChain 0 1 policies8[0]!.pieces.toList)
    (hterminal : MomentAvailable curve 20)
    (halloc : ∀i : Fin policies8[0]!.pieces.size,PieceAllocationValid policies8[0]!.phi.size policies8[0]!.pieces[i.val]!)
    (hv : ∀i : Fin policies8[0]!.pieces.size,∀r,ResourcePhysicalShape 8 policies8[0]! (resourceAt policies8[0]!.pieces[i.val]! r))
    (hav : ∀i : Fin policies8[0]!.pieces.size,∀r,MomentAvailable coefficient (resourceAt policies8[0]!.pieces[i.val]! r).order) :
    SourcePowerBound
      (fun P R=>boxMinorIntegral 8 8 (64*P) P R (fun i=>P^(phiReal policies8[0]! i)))
      (terminalMaximum entry.evaluation:ℝ) := by
  let p : Policy:=policies8[0]!
  let params:=terminalParameters 8 curve p
  let q : ℝ:=1-total (phiReal p)
  let amp : ℝ:=amplitude 8 (phiReal p)
  let b : ℝ:=12*q
  let rho : ℝ:=((8*(8-p.phi.size):ℕ):ℝ)+1
  let B : ℝ:=boundaryErrorConstant params
  have hB : 0≤B:=boundaryErrorConstant_nonneg params
  have hrho : 0<rho:=by dsimp [rho]; positivity
  have hφ:=phiReal_pos hguard
  have hshift:=phiReal_shift_pos (by norm_num : 0<8) hguard
  have hq : 0<q:=length_pos (by decide : p.phi.size<8) (phiReal p) (fun i=>(hshift i).le)
  have hparams:=frozen_parameters curve
  have hΔ : 0≤((delta 8 curve 20).getD 0:ℝ):=delta_getD_nonneg hterminal
  have hslope : 0≤(params.slope:ℝ):=by rw [hparams.2.1]; positivity
  intro ε hε
  let δ : ℝ:=ε/4
  have hδ : 0<δ:=by dsimp [δ]; positivity
  obtain ⟨ηF,CF,PF,hηF,hCF,hPF,hpoint⟩:=policy_piece_source_pointwise 8 107520 p .zero
    (by norm_num) (by norm_num) (by decide) reduction8_6 64 (by norm_num)
    hguard coefficient hcoeff halloc hv hav (params.top:ℝ) hrho.le hδ
  obtain ⟨ηg,hηg,CG,hCG,hmean⟩:=even_excess_height_lintegral_dilated
    (k:=8) (r:=10) (by norm_num) (by norm_num) hq (by norm_num : (1:ℝ)≤64)
    (delta_getD_admissible hcurve hterminal) hδ
  obtain ⟨ηL,hηL,CL,hCL,PL,hPL,hsecond⟩:=frozen_source_second_lintegral hδ
  obtain ⟨CT,hCT,hintegral⟩:=policy_terminal_integral_rpow 8 curve coefficient p entry
    hheight hrec hguard hchain hslope (by norm_num : (0:ℝ)≤5/4) hδ
  let η₀ : ℝ:=min ηF (min ηg (min ηL (ε/(4*(B*rho+1)))))
  have hη₀ : 0<η₀:=lt_min hηF (lt_min hηg (lt_min hηL (div_pos hε (by positivity))))
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηle
  have hηF' : η≤ηF:=hηle.trans (min_le_left _ _)
  have hηg' : η≤ηg:=(hηle.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηL' : η≤ηL:=((hηle.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηB : B*(rho*η)≤δ:=by
    have hh : η≤ε/(4*(B*rho+1)):=
      ((hηle.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hm:=(le_div_iff₀ (by positivity : (0:ℝ)<4*(B*rho+1))).mp hh
    dsimp [δ]
    nlinarith
  let c : ℝ:=(64:ℝ)^8/64
  have hc : 0<c:=by norm_num [c]
  let P₀ : ℝ:=max (max PF PL) (c^(1/η))
  let CJ : ℝ:=CF^(3/4:ℝ)*CG*CT
  have hCJ : 0<CJ:=by dsimp [CJ]; positivity
  let C : ℝ:=CL^(1/5:ℝ)*CJ^(4/5:ℝ)
  have hC : 0<C:=by dsimp [C]; positivity
  refine ⟨C,hC,P₀,(hPL.trans ((le_max_right _ _).trans (le_max_left _ _))),?_⟩
  intro P hPP
  have hPF' : PF≤P:=((le_max_left _ _).trans (le_max_left _ _)).trans hPP
  have hPL' : PL≤P:=((le_max_right _ _).trans (le_max_left _ _)).trans hPP
  have hP2 : 2≤P:=hPF.trans hPF'
  have hP : 1≤P:=by linarith
  have hPgt : 1<P:=by linarith
  have hPp : 0<P:=by linarith
  have hR : 1≤P^η:=Real.one_le_rpow hP hη.le
  have hscale : c≤P^η:=NormalizedCoefficient.fixed_constant_rpow_bound hc hη ((le_max_right _ _).trans hPP)
  let M : Fin p.phi.size→ℝ:=fun i=>P^(phiReal p i)
  let Y : ℝ:=boxSmoothLength (64*P) M
  let V : ℝ:=P^(8*q)
  let μ:=volume.restrict (boxMinorSet 8 (64*P) (P^η) M)
  let H:=height V
  let ell:=normalizedHeight P V
  let F : ℝ→ℝ≥0∞:=fun α=>ENNReal.ofReal ‖boxSourceFamily 8 (64*P) P (P^η) M α‖
  let G : ℝ→ℝ≥0∞:=fun α=>ENNReal.ofReal ‖smoothWeyl 8 Y (P^η) α‖
  have hY : Y=64*P^q:=boxSmoothLength_power hPp 64 (phiReal p) (fun i=>(hφ i).le)
  have hVp : 0<V:=Real.rpow_pos_of_pos hPp _
  have hHmeas : Measurable H:=measurable_height hVp
  have hFmeas : Measurable F:=(continuous_boxSourceFamily 8 (64*P) P (P^η) M).norm.measurable.ennreal_ofReal
  have hGmeas : Measurable G:=(continuous_smoothWeyl 8 Y (P^η)).norm.measurable.ennreal_ofReal
  have hmem : ∀ᵐα ∂μ,α∈boxMinorSet 8 (64*P) (P^η) M:=
    ae_restrict_mem (boxMinorSet_measurable 8 (64*P) (P^η) M)
  have hlo : ∀ᵐα ∂μ,1≤H α:=Filter.Eventually.of_forall (one_le_height V)
  have heq : ∀ᵐα ∂μ,H α=P^(ell α):=
    Filter.Eventually.of_forall (fun α=>(height_eq_normalized hPgt V α).symm)
  have hrange : ∀ᵐα ∂μ,1-rho*η≤ell α ∧ ell α≤(params.top:ℝ):=by
    filter_upwards [hmem] with α hα
    have hh:=source_minor_normalized_bounds (k:=8) (by norm_num) (by norm_num : (1:ℝ)≤64)
      hPgt hR le_rfl (phiReal p) (fun i=>(hφ i).le) hq.le hscale
      (show ¬MajorAtCutoff (64*P) ((boxConductor 8 (64*P) M/(64*P))*(P^η)^(((8*(8-p.phi.size):ℕ):ℝ))) α by
        simpa only [Real.rpow_natCast] using hα.2)
    refine ⟨hh.1.le,?_⟩
    rw [terminalParameters_top_cast]
    convert hh.2 using 1 <;> ring
  let AF : ℝ:=CF^(3/5:ℝ)*P^((3/5:ℝ)*δ-(1/5:ℝ)*amp-(4/5:ℝ)*b)
  let KG : ℝ:=CG*P^(b+δ)
  have hAF : 0<AF:=by dsimp [AF]; positivity
  have hKG : 0<KG:=by dsimp [KG]; positivity
  have hp : ∀ᵐα ∂μ,∀i : Fin p.pieces.size,
      (F α)^(3/5:ℝ)≤ENNReal.ofReal AF*ENNReal.ofReal
        (P^((params.base:ℝ)-(params.scale:ℝ)*min 1 (pieceSavingReal 8 p coefficient p.pieces[i.val]! (ell α)))):=by
    filter_upwards [hmem,hrange] with α hα hrangeα i
    have hm:=source_minor_height_power (k:=8) (by norm_num) (by norm_num : (1:ℝ)≤64)
      hPgt hη.le (phiReal p) (fun i=>(hφ i).le) hscale hα
    have hb:=hpoint P hPF' (P^η) hR (Real.rpow_le_rpow_of_exponent_le hP hηF')
      α (ell α) ⟨normalizedHeight_nonneg hPgt V α,hrangeα.2⟩
      (by simpa only [sumQ_cast_eq_total] using hm)
      (by simpa only [sumQ_cast_eq_total] using (height_eq_normalized hPgt V α).le) i
    simp only [root,div_one] at hb
    rw [hparams.1,hparams.2.2]
    have hs := auxiliary_powered_pointwise
      (X:=‖boxSourceFamily 8 (64*P) P (P^η) M α‖) (C:=CF) (P:=P)
      (a:=amp) (b:=b) (δ:=δ)
      (S:=min 1 (pieceSavingReal 8 p coefficient p.pieces[i.val]! (ell α)))
      hPp hCF.le (norm_nonneg _) hb
    simpa only [F,AF,amp,b,q,p,Nat.cast_ofNat,Nat.cast_one,Rat.cast_ofNat,Rat.cast_one] using hs
  have hm (Z : ℝ) (hZ : 1≤Z) (_ : Z≤4*P^(params.top:ℝ)) :
      (∫⁻α in {α|H α≤Z},(G α)^(20:ℕ) ∂μ)≤
        ENNReal.ofReal KG*ENNReal.ofReal (Z^((params.slope:ℝ)*(5/4:ℝ))):=by
    have hsub : μ≤volume.restrict (Set.Ioc 0 1):=Measure.restrict_mono_set volume Set.inter_subset_left
    have hh:=hmean P hP Z (P^η) hZ hR (Real.rpow_le_rpow_of_exponent_le hP hηg')
    rw [←hY] at hh
    simp only [Nat.reduceMul,ENNReal.ofReal_pow (norm_nonneg _)] at hh
    have hs : (params.slope:ℝ)*(5/4:ℝ)=2*((delta 8 curve 20).getD 0:ℝ)/8:=by
      rw [hparams.2.1]
      ring
    rw [hs]
    convert (lintegral_mono' (Measure.restrict_mono_measure hsub _) le_rfl).trans hh using 1 <;>
      norm_num [KG,b]
  have hJ:=hintegral P hP (rho*η) (mul_nonneg hrho.le hη.le) ℝ μ H ell
    (fun α=>(F α)^(3/5:ℝ)) (fun α=>(G α)^(20:ℕ)) hHmeas (hGmeas.pow_const _) hlo heq hrange
    (ENNReal.ofReal AF) (ENNReal.ofReal KG) hp hm
  simp_rw [←ENNReal.rpow_mul] at hJ
  norm_num only [show (3/5:ℝ)*(5/4)=3/4 by norm_num] at hJ
  let eJ : ℝ:=(5/4:ℝ)*((terminalMaximum entry.evaluation:ℝ)+B*(rho*η))-amp/4+(11/4:ℝ)*δ
  have hidJ : (ENNReal.ofReal AF)^(5/4:ℝ)*ENNReal.ofReal KG*
      ENNReal.ofReal (CT*P^(((terminalMaximum entry.evaluation:ℝ)+B*(rho*η))*(5/4:ℝ)+δ))=
      ENNReal.ofReal (CJ*P^eJ):=by
    exact auxiliary_inner_scalar hPp hCF hCG hCT
  rw [hidJ] at hJ
  have hL : (∫⁻α,(F α)^(2:ℕ) ∂μ)≤ENNReal.ofReal (CL*P^(amp+δ)):=by
    have hsub : μ≤volume.restrict (Set.Ioc 0 1):=Measure.restrict_mono_set volume Set.inter_subset_left
    exact (lintegral_mono' hsub le_rfl).trans
      (hsecond P hPL' (P^η) hR (Real.rpow_le_rpow_of_exponent_le hP hηL'))
  have hout:=(auxiliary_global_split hFmeas.aemeasurable hGmeas.aemeasurable).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow hL (by norm_num : (0:ℝ)≤1/5))
      (ENNReal.rpow_le_rpow hJ (by norm_num : (0:ℝ)≤4/5)))
  have hleft : (∫⁻α,F α*(G α)^(16:ℕ) ∂μ)=ENNReal.ofReal (boxMinorIntegral 8 8 (64*P) P (P^η) M):=by
    rw [boxMinorIntegral_lintegral]
    simp only [F,G,Y,μ,Nat.reduceMul,ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hleft,ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),←ENNReal.ofReal_mul (by positivity)] at hout
  have hscalar : (CL*P^(amp+δ))^(1/5:ℝ)*(CJ*P^eJ)^(4/5:ℝ)=
      C*P^((terminalMaximum entry.evaluation:ℝ)+B*(rho*η)+(12/5:ℝ)*δ):=by
    exact auxiliary_outer_scalar hPp hCL hCJ
  rw [hscalar] at hout
  have hreal:=(ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hout
  change |boxMinorIntegral 8 8 (64*P) P (P^η) M|≤_
  have hnon : 0≤boxMinorIntegral 8 8 (64*P) P (P^η) M:=
    integral_nonneg (fun α=>mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
  rw [abs_of_nonneg hnon]
  apply hreal.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hP
  dsimp [δ] at hηB ⊢
  linarith

#print axioms auxiliary_minor_source_bound
end Waring.PolicyCompletionAuxiliaryMinor
