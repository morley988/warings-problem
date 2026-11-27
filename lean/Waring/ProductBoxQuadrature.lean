import Waring.ProductBoxGridIntegral

/-! # A quantitative product-box quadrature theorem

Separate periodicity is used in each coordinate. Repeated one-dimensional
Abel summation costs only L*q/M relative to the full product box.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion

/-- The literal one-coordinate derivative bounds, recursively on slices. -/
def BoxRegular : (L : ℕ) → ℝ → ℝ → ℝ → ((Fin L → ℝ) → ℂ) → Prop
  | 0,_,_,_,_ => True
  | L+1,M,B,D,f =>
      (∀ y : Fin L → ℝ,(∀ i,y i ∈ Set.Icc 0 M) →
        (∀ t,DifferentiableAt ℝ (fun t => f (Fin.cons t y)) t) ∧
        Continuous (deriv (fun t => f (Fin.cons t y))) ∧
        ‖f (Fin.cons M y)‖≤B ∧
        ∀ t∈Set.Icc 0 M,‖deriv (fun t => f (Fin.cons t y)) t‖≤D) ∧
      ∀ t∈Set.Icc 0 M,BoxRegular L M B D (fun y => f (Fin.cons t y))

theorem product_box_quadrature (L M q : ℕ) (hM : 0<M) (hq : 0<q)
    {B D : ℝ} (hB : 0≤B) (hD : 0≤D) (c : (Fin L → ℕ) → ℂ)
    (hc : ∀ x,‖c x‖≤1) (hper : GridPeriodic L q c)
    (f : (Fin L → ℝ) → ℂ) (hf : Continuous f) (hreg : BoxRegular L M B D f) :
    ‖gridSum L M (fun x => f (fun i => (x i : ℝ))*c x)-gridMean L q c*boxIntegral L M f‖ ≤
      3*(L : ℝ)*q*(B+(M : ℝ)*D)*(M : ℝ)^L/(M : ℝ) := by
  have hMr : (0 : ℝ)<M := by exact_mod_cast hM
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  induction L with
  | zero =>
    have he : (fun i : Fin 0 => ((Fin.elim0 i : ℕ) : ℝ))=Fin.elim0 := Subsingleton.elim _ _
    simp [gridSum,gridMean,boxIntegral,he,mul_comm]
  | succ L ih =>
    let c0 := headMean q c
    let G := fun t : ℝ => gridSum L M (fun y => f (Fin.cons t (fun i => (y i : ℝ)))*c0 y)
    let E : ℝ := 3*(q : ℝ)*(B+(M : ℝ)*D)
    have hE : 0≤E := by dsimp [E]; positivity
    have hG : Continuous G := by
      apply continuous_gridSum
      intro y
      exact (hf.comp (continuous_cons continuous_id continuous_const)).mul continuous_const
    have hI : Continuous (fun t : ℝ => boxIntegral L M (fun y => f (Fin.cons t y))) := by
      apply continuous_boxIntegral
      exact hf.comp (continuous_cons continuous_fst continuous_snd)
    have hfirst : ‖gridSum (L+1) M (fun x => f (fun i => (x i : ℝ))*c x)-
        ∫ t in Set.Icc 0 (M : ℝ),G t‖≤E*(M : ℝ)^L := by
      have hsum : gridSum (L+1) M (fun x => f (fun i => (x i : ℝ))*c x)=
          gridSum L M (fun y => ∑ n∈Finset.Icc 1 M,
            f (Fin.cons (n : ℝ) (fun i => (y i : ℝ)))*c (Fin.cons n y)) := by
        rw [gridSum,gridSum_sum]
        apply Finset.sum_congr rfl
        intro n _
        congr 1
        funext y
        have he : (fun i : Fin (L+1) => (((Fin.cons n y : Fin (L+1) → ℕ) i) : ℝ))=
            (Fin.cons (n : ℝ) (fun i => (y i : ℝ)) : Fin (L+1) → ℝ) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> rfl
        rw [he]
      have hint : (∫ t in Set.Icc 0 (M : ℝ),G t)=
          gridSum L M (fun y => c0 y*(∫ t in Set.Icc 0 (M : ℝ),
            f (Fin.cons t (fun i => (y i : ℝ))))) := by
        rw [show G=(fun t => gridSum L M (fun y =>
          f (Fin.cons t (fun i => (y i : ℝ)))*c0 y)) from rfl,← gridSum_integral]
        congr 1
        funext y
        rw [integral_mul_const,mul_comm]
        intro y
        exact (hf.comp (continuous_cons continuous_id continuous_const)).mul continuous_const
      rw [hsum,hint,← gridSum_sub]
      apply gridSum_norm_le L M hE
      intro y hy
      have hyreal : ∀ i,(y i : ℝ) ∈ Set.Icc 0 (M : ℝ) := by
        intro i
        exact ⟨Nat.cast_nonneg _,by exact_mod_cast (Finset.mem_Icc.mp (hy i)).2⟩
      obtain ⟨hdiff,hder,hend,hbound⟩ := hreg.1 (fun i => (y i : ℝ)) hyreal
      have hh := norm_positive_sum_sub_mean_integral_le hq (hper.1 y)
        (fun n => hc (Fin.cons n y)) hMr.le hdiff hder hend hbound
      simpa only [Nat.floor_natCast,intervalIntegral.integral_of_le hMr.le,
        integral_Icc_eq_integral_Ioc,c0,headMean,E] using hh
    have hsecond : ‖(∫ t in Set.Icc 0 (M : ℝ),G t)-
        gridMean (L+1) q c*boxIntegral (L+1) M f‖≤
          (3*(L : ℝ)*q*(B+(M : ℝ)*D)*(M : ℝ)^L/(M : ℝ))*(M : ℝ) := by
      have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 (M : ℝ)) :
          ‖G t-gridMean L q c0*boxIntegral L M (fun y => f (Fin.cons t y))‖≤
            3*(L : ℝ)*q*(B+(M : ℝ)*D)*(M : ℝ)^L/(M : ℝ) :=
        ih c0 (headMean_norm_le_one hq hc) (headMean_periodic hper)
          (fun y => f (Fin.cons t y)) (hf.comp (continuous_cons continuous_const continuous_id))
          (hreg.2 t ht)
      have he : (∫ t in Set.Icc 0 (M : ℝ),
          G t-gridMean L q c0*boxIntegral L M (fun y => f (Fin.cons t y)))=
          (∫ t in Set.Icc 0 (M : ℝ),G t)-gridMean (L+1) q c*boxIntegral (L+1) M f := by
        rw [integral_sub (hG.continuousOn.integrableOn_compact isCompact_Icc)
          ((continuous_const.mul hI).continuousOn.integrableOn_compact isCompact_Icc),
          integral_const_mul,gridMean_headMean]
        rfl
      rw [← he]
      have hh := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
        (s := Set.Icc 0 (M : ℝ)) (measure_Icc_lt_top) hpoint
      simpa only [Real.volume_real_Icc,sub_zero,max_eq_left hMr.le] using hh
    calc
      _ ≤ ‖gridSum (L+1) M (fun x => f (fun i => (x i : ℝ))*c x)-
          ∫ t in Set.Icc 0 (M : ℝ),G t‖+
          ‖(∫ t in Set.Icc 0 (M : ℝ),G t)-gridMean (L+1) q c*boxIntegral (L+1) M f‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hfirst hsecond
      _ = _ := by dsimp [E]; push_cast; rw [pow_succ]; field_simp; ring

#print axioms product_box_quadrature
end Waring.ProductBox
