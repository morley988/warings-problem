import Waring.EndgameCompletionMinorAverage
import Waring.EndgameCompletionMinorCount
import Waring.CriticalVMVT

/-!
# Actual ordinary minor-arc transport to critical VMVT

All projections, translations, completions, reciprocal averages and count
normalizations have been proved in the preceding modules. This file
integrates their pointwise inequality on the literal minor region.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace Waring.EndgameCompletion
open QuadraticModulation MixedEndgame

def ordinaryMinorRegion (k : ℕ) (P : ℝ) : Set ℝ :=
  Set.Ioc 0 1\ordinaryBroadMajor k P

theorem ordinaryMinorRegion_measurable (k : ℕ) (P : ℝ) :
    MeasurableSet (ordinaryMinorRegion k P) :=
  measurableSet_Ioc.diff (ordinaryBroadMajor_measurable k P)

theorem ordinaryMinorRegion_subset (k : ℕ) (P : ℝ) :
    ordinaryMinorRegion k P⊆Set.Ioc 0 1 := Set.diff_subset

theorem ordinary_major_minor_cover (k : ℕ) (P : ℝ) :
    ordinaryBroadMajor k P∪ordinaryMinorRegion k P=Set.Ioc 0 1 :=
  Set.union_diff_cancel (ordinaryBroadMajor_subset k P)

theorem positiveNode_sum_eq_ordinary (k N : ℕ) (θ : ℝ) :
    (∑ n : Fin N,e (θ*(positiveNode N n : ℝ)^k))=ordinaryWeyl k N θ := by
  classical
  unfold ordinaryWeyl ordinaryNumbers
  rw [Nat.floor_natCast]
  apply Finset.sum_bij (fun n _=>n.val+1)
  · intro n _
    apply Finset.mem_Icc.mpr
    have hn := n.isLt
    omega
  · intro n _ m _ h
    apply Fin.ext
    omega
  · intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hl,hu⟩
    refine ⟨⟨m-1,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp only
    omega
  · intro n _
    rw [phase_eq_e]
    simp [positiveNode]

theorem ordinary_lower_projection (r s N : ℕ) (hN : 1≤N) (θ : ℝ) :
    ‖ordinaryWeyl (r+2) N θ‖^(2*s)≤
      (((s : ℝ)+1)^r*(N : ℝ)^(∑ j : Fin r,(j.val+1)))*projectedSlice r s N 0 θ := by
  have hn0 (n : Fin N) : 0≤positiveNode N n := by dsimp [positiveNode]; omega
  have hnN (n : Fin N) : positiveNode N n≤N := by
    dsimp [positiveNode]
    have h := n.isLt
    omega
  have hh := polynomial_lower_projection r s N hN (positiveNode N)
    (fun n=>e (θ*(positiveNode N n : ℝ)^(r+2))) hn0 hnN
  rw [positiveNode_sum_eq_ordinary] at hh
  simpa only [projectedSlice,zero_mul,add_zero] using hh

theorem completionMass_pow_le_rpow (p : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → completionMass N^p≤C*(N : ℝ)^ε := by
  obtain ⟨D,hD,hbound⟩ := DyadicLogLoss.clog_depth_pow_le_rpow p hε
  refine ⟨4^p*D,by positivity,?_⟩
  intro N hN
  calc
    _ ≤ (4*((Nat.clog 2 N+1 : ℕ) : ℝ))^p :=
      pow_le_pow_left₀ (completionMass_nonneg N) (completionMass_le_dyadic N hN) p
    _ = 4^p*(((Nat.clog 2 N+1 : ℕ) : ℝ)^p) := mul_pow _ _ _
    _ ≤ 4^p*(D*(N : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left (hbound N (by omega)) (by positivity)
    _ = _ := by ring

theorem continuous_projectedSlice_mean (r s N : ℕ) :
    Continuous (fun θ=>∫ t in (0 : ℝ)..1,projectedSlice r s N t θ) := by
  simp_rw [projectedSlice_integral]
  apply continuous_projectedMoment (r+1) s (positiveNode N)
  intro n
  exact continuous_e.comp (continuous_id.mul continuous_const)

/-- The actual minor `2s`-moment is bounded by the actual `J_(s,r+2)(2N)`
count, with the full one-power saving in its polynomial prefactor. -/
theorem ordinary_minor_moment_to_VMVT (r s : ℕ) (hr : 1≤r) (hs : 1≤s)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      (∫ θ in ordinaryMinorRegion (r+2) N,‖ordinaryWeyl (r+2) N θ‖^(2*s))≤
        C*(N : ℝ)^(((∑ j : Fin r,(j.val+1)) : ℕ)+(r : ℝ)+ε)*
          (GafniTao.fordVinogradovMomentNat s (r+2) (2*N) : ℝ) := by
  obtain ⟨A,hA,hmass⟩ := completionMass_pow_le_rpow (2*s) (half_pos hε)
  obtain ⟨B,hB,hminor⟩ := projectedSlice_minor_bound r s hr hs (half_pos hε)
  let C : ℝ := ((s : ℝ)+1)^r*A*B
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN
  let J := ∑ j : Fin r,(j.val+1)
  let F := fun θ=>∫ t in (0 : ℝ)..1,projectedSlice r s (2*N) t θ
  let K := C*(N : ℝ)^((J : ℝ)+(r : ℝ)+ε)
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hF0 (θ : ℝ) : 0≤F θ :=
    intervalIntegral.integral_nonneg zero_le_one (fun t _=>projectedSlice_nonneg r s (2*N) t θ)
  have hFc : Continuous F := continuous_projectedSlice_mean r s (2*N)
  have hK0 : 0≤K := by dsimp [K]; positivity
  have hpowers : (N : ℝ)^J*(N : ℝ)^(ε/2)*(N : ℝ)^((r : ℝ)+ε/2)=
      (N : ℝ)^((J : ℝ)+(r : ℝ)+ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hNpos,← Real.rpow_add hNpos]
    congr 1
    ring
  have hpoint (θ : ℝ) (hθ : θ∈ordinaryMinorRegion (r+2) N) :
      ‖ordinaryWeyl (r+2) N θ‖^(2*s)≤K*F θ := by
    have hFt := hF0 θ
    have hm := hminor N hN θ hθ.1 hθ.2
    calc
      _ ≤ (((s : ℝ)+1)^r*(N : ℝ)^J)*
          (completionMass N^(2*s)*(B*(N : ℝ)^((r : ℝ)+ε/2)*F θ)) :=
        (ordinary_lower_projection r s N hN θ).trans
          (mul_le_mul_of_nonneg_left hm (by positivity))
      _ ≤ (((s : ℝ)+1)^r*(N : ℝ)^J)*
          ((A*(N : ℝ)^(ε/2))*(B*(N : ℝ)^((r : ℝ)+ε/2)*F θ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (hmass N hN) (by positivity)
      _ = _ := by
        dsimp [K,C]
        calc
          _ = (((s : ℝ)+1)^r*A*B)*
              ((N : ℝ)^J*(N : ℝ)^(ε/2)*(N : ℝ)^((r : ℝ)+ε/2))*F θ := by ring
          _ = _ := by rw [hpowers]
  have hsub := (ordinaryMinorRegion_subset (r+2) N).trans Set.Ioc_subset_Icc_self
  have hleft : IntegrableOn (fun θ=>‖ordinaryWeyl (r+2) N θ‖^(2*s))
      (ordinaryMinorRegion (r+2) N) :=
    ((continuous_ordinary (r+2) N).norm.pow (2*s)).integrableOn_Icc.mono_set hsub
  have hright : IntegrableOn (fun θ=>K*F θ) (ordinaryMinorRegion (r+2) N) :=
    (continuous_const.mul hFc).integrableOn_Icc.mono_set hsub
  calc
    _ ≤ ∫ θ in ordinaryMinorRegion (r+2) N,K*F θ :=
      setIntegral_mono_on hleft hright (ordinaryMinorRegion_measurable (r+2) N) hpoint
    _ = K*(∫ θ in ordinaryMinorRegion (r+2) N,F θ) := integral_const_mul _ _
    _ ≤ K*(∫ θ in Set.Ioc (0 : ℝ) 1,F θ) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_mono_set ((hFc.intervalIntegrable 0 1).1)
          (Filter.Eventually.of_forall hF0)
          (Filter.Eventually.of_forall (ordinaryMinorRegion_subset (r+2) N))) hK0
    _ = _ := by
      rw [← intervalIntegral.integral_of_le zero_le_one,projectedSlice_full_integral]

#print axioms ordinary_minor_moment_to_VMVT

theorem degree8_ordinary_minor72_real {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      (∫ θ in ordinaryMinorRegion 8 N,‖ordinaryWeyl 8 N θ‖^72)≤
        C*(N : ℝ)^(63+ε : ℝ) := by
  obtain ⟨A,hA,ha⟩ := ordinary_minor_moment_to_VMVT 6 36 (by norm_num) (by norm_num) (half_pos hε)
  obtain ⟨B,hB,hb⟩ := CriticalVMVT.degree8 (half_pos hε)
  refine ⟨A*B*(2 : ℝ)^(36+ε/2 : ℝ),by positivity,?_⟩
  intro N hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ht := ha N hN
  norm_num [Fin.sum_univ_succ] at ht
  have hc := hb (2*N) (by omega)
  have hpow : (N : ℝ)^(27+ε/2 : ℝ)*(N : ℝ)^(36+ε/2 : ℝ)=
      (N : ℝ)^(63+ε : ℝ) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ A*(N : ℝ)^(27+ε/2 : ℝ)*(GafniTao.fordVinogradovMomentNat 36 8 (2*N) : ℝ) := ht
    _ ≤ A*(N : ℝ)^(27+ε/2 : ℝ)*(B*((2*N : ℕ) : ℝ)^(36+ε/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hn.le]
      calc
        _ = (A*B*(2 : ℝ)^(36+ε/2 : ℝ))*
            ((N : ℝ)^(27+ε/2 : ℝ)*(N : ℝ)^(36+ε/2 : ℝ)) := by ring
        _ = _ := by rw [hpow]

theorem degree9_ordinary_minor90_real {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      (∫ θ in ordinaryMinorRegion 9 N,‖ordinaryWeyl 9 N θ‖^90)≤
        C*(N : ℝ)^(80+ε : ℝ) := by
  obtain ⟨A,hA,ha⟩ := ordinary_minor_moment_to_VMVT 7 45 (by norm_num) (by norm_num) (half_pos hε)
  obtain ⟨B,hB,hb⟩ := CriticalVMVT.degree9 (half_pos hε)
  refine ⟨A*B*(2 : ℝ)^(45+ε/2 : ℝ),by positivity,?_⟩
  intro N hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ht := ha N hN
  norm_num [Fin.sum_univ_succ] at ht
  have hc := hb (2*N) (by omega)
  have hpow : (N : ℝ)^(35+ε/2 : ℝ)*(N : ℝ)^(45+ε/2 : ℝ)=
      (N : ℝ)^(80+ε : ℝ) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ A*(N : ℝ)^(35+ε/2 : ℝ)*(GafniTao.fordVinogradovMomentNat 45 9 (2*N) : ℝ) := ht
    _ ≤ A*(N : ℝ)^(35+ε/2 : ℝ)*(B*((2*N : ℕ) : ℝ)^(45+ε/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hn.le]
      calc
        _ = (A*B*(2 : ℝ)^(45+ε/2 : ℝ))*
            ((N : ℝ)^(35+ε/2 : ℝ)*(N : ℝ)^(45+ε/2 : ℝ)) := by ring
        _ = _ := by rw [hpow]

theorem ordinaryArcMoment_minor_eq (k p N : ℕ) :
    ordinaryArcMoment k p N (ordinaryMinorRegion k N)=
      ENNReal.ofReal (∫ θ in ordinaryMinorRegion k N,‖ordinaryWeyl k N θ‖^p) := by
  have hi : IntegrableOn (fun θ=>‖ordinaryWeyl k N θ‖^p) (ordinaryMinorRegion k N) :=
    ((continuous_ordinary k N).norm.pow p).integrableOn_Icc.mono_set
      ((ordinaryMinorRegion_subset k N).trans Set.Ioc_subset_Icc_self)
  rw [ordinaryArcMoment]
  simp only [absoluteOrdinary,← ENNReal.ofReal_pow (norm_nonneg _)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun θ=>pow_nonneg (norm_nonneg _) p))).symm

/-- Unconditional actual degree-eight minor 72nd moment, with every
positive epsilon and one uniform constant before all integer scales. -/
theorem degree8_ordinary_minor72 {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      ordinaryArcMoment 8 72 N (ordinaryMinorRegion 8 N)≤
        ENNReal.ofReal (C*(N : ℝ)^(63+ε : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := degree8_ordinary_minor72_real hε
  refine ⟨C,hC,fun N hN=>?_⟩
  rw [ordinaryArcMoment_minor_eq]
  exact ENNReal.ofReal_le_ofReal (hbound N hN)

/-- Unconditional actual degree-nine minor 90th moment. -/
theorem degree9_ordinary_minor90 {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      ordinaryArcMoment 9 90 N (ordinaryMinorRegion 9 N)≤
        ENNReal.ofReal (C*(N : ℝ)^(80+ε : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := degree9_ordinary_minor90_real hε
  refine ⟨C,hC,fun N hN=>?_⟩
  rw [ordinaryArcMoment_minor_eq]
  exact ENNReal.ofReal_le_ofReal (hbound N hN)

#print axioms degree8_ordinary_minor72
#print axioms degree9_ordinary_minor90
end Waring.EndgameCompletion
