import Waring.EndgameCompletionBroadArcs
import Waring.CriticalVMVTMinorSpacing

/-!
# Short-multiple separation on the actual ordinary minor region

An arbitrary nearest-integer approximation is reduced before it is put in
the literal major-region union. The rational endpoint one uses the translate
of the reduced residue zero modulo one.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace Waring.EndgameCompletion
open MixedEndgame RestrictedSmoothArcs RationalSpacing

theorem mem_periodicMajorRegion_of_rat (S : Finset ℕ+) (δ α : ℝ)
    (hα : α ∈ Set.Ioc 0 1) (r : ℚ)
    (hr0 : (0 : ℝ) ≤ r) (hr1 : (r : ℝ) ≤ 1)
    (hq : (⟨r.den,r.pos⟩ : ℕ+) ∈ S)
    (herr : |(r.den : ℝ)*α-(r.num : ℝ)| ≤ δ) :
    α ∈ periodicMajorRegion S δ := by
  classical
  by_cases hr : r=1
  · subst r
    let q : ℕ+ := ⟨1,by norm_num⟩
    let a : (ZMod (q : ℕ))ˣ := 1
    apply (mem_periodicMajorRegion S δ α).mpr
    refine ⟨hα,q,by simpa [q] using hq,a,Or.inr ?_⟩
    have hp : arcLabelRat ⟨q,a⟩=0 := by
      apply Rat.ext
      · simp [arcLabelRat,q,a]
      · simp [arcLabelRat,q,a]
    rw [hp]
    have hh : |α-1|≤δ := by simpa using herr
    simpa only [Rat.cast_zero,Rat.den_zero,Nat.cast_one,div_one,zero_sub,zero_add,
      Set.mem_Icc] using (show -δ+1≤α ∧ α≤δ+1 by
        rcases abs_le.mp hh with ⟨hl,hu⟩
        constructor <;> linarith)
  · have hrlt : (r : ℝ)<1 := lt_of_le_of_ne hr1 (by exact_mod_cast hr)
    have hnum0 : 0≤r.num := Rat.num_nonneg.mpr (by exact_mod_cast hr0)
    have hnum : (r.num.natAbs : ℤ)=r.num := by
      rw [Int.natCast_natAbs,abs_of_nonneg hnum0]
    have hnumlt : r.num.natAbs<r.den := by
      have hd : (0 : ℝ)<r.den := by exact_mod_cast r.pos
      rw [Rat.cast_def,div_lt_one hd] at hrlt
      have he : (r.num.natAbs : ℝ)=(r.num : ℝ) := by
        simpa only [Int.cast_natCast] using congrArg (fun z : ℤ=>(z : ℝ)) hnum
      rw [← he] at hrlt
      exact_mod_cast hrlt
    let q : ℕ+ := ⟨r.den,r.pos⟩
    let a : (ZMod (q : ℕ))ˣ := ZMod.unitOfCoprime r.num.natAbs r.reduced
    have ha : ((a : ZMod (q : ℕ)).val)=r.num.natAbs := by
      simp only [a,ZMod.coe_unitOfCoprime,ZMod.val_natCast,q,PNat.mk_coe]
      exact Nat.mod_eq_of_lt hnumlt
    have hp : arcLabelRat ⟨q,a⟩=r := by
      apply Rat.ext
      · change ((a : ZMod (q : ℕ)).val : ℤ)=r.num
        rw [ha,hnum]
      · rfl
    apply (mem_periodicMajorRegion S δ α).mpr
    refine ⟨hα,q,hq,a,Or.inl ?_⟩
    rw [hp]
    exact herr

theorem mem_periodicMajorRegion_of_unreduced (S : Finset ℕ+) (δ α : ℝ)
    (hα : α ∈ Set.Ioc 0 1) (a : ℤ) (d : ℕ) (hd : 0<d)
    (ha0 : 0≤a) (had : a≤d)
    (hden : ∀ q : ℕ+, (q : ℕ)≤d → q∈S)
    (herr : |(d : ℝ)*α-(a : ℝ)|≤δ) :
    α∈periodicMajorRegion S δ := by
  let r : ℚ := Rat.divInt a (d : ℤ)
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hdenZ : (r.den : ℤ)≤d :=
    Int.le_of_dvd (by exact_mod_cast hd) (Rat.den_dvd a (d : ℤ))
  have hdenN : r.den≤d := by exact_mod_cast hdenZ
  have hcast : (r : ℝ)=(a : ℝ)/(d : ℝ) := by
    dsimp [r]
    rw [Rat.cast_divInt]
    norm_cast
  have hr0 : (0 : ℝ)≤r := by rw [hcast]; positivity
  have hr1 : (r : ℝ)≤1 := by
    rw [hcast,div_le_one hdR]
    exact_mod_cast had
  have he : (d : ℝ)*|α-(r : ℝ)|=|(d : ℝ)*α-(a : ℝ)| := by
    calc
      _ = |(d : ℝ)*(α-(r : ℝ))| := by rw [abs_mul,abs_of_pos hdR]
      _ = _ := by
        congr 1
        rw [hcast]
        field_simp
  apply mem_periodicMajorRegion_of_rat S δ α hα r hr0 hr1
    (hden ⟨r.den,r.pos⟩ hdenN)
  rw [RationalHeight.denominator_error]
  calc
    _ ≤ (d : ℝ)*|α-(r : ℝ)| :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hdenN) (abs_nonneg _)
    _ ≤ δ := by rw [he]; exact herr

theorem round_monotone_real : Monotone (round : ℝ→ℤ) := by
  intro x y hxy
  rw [round_eq,round_eq]
  exact Int.floor_mono (add_le_add_right hxy _)

/-- The literal broad-major complement supplies every separation premise
used in the finite reciprocal-average estimate. -/
theorem ordinary_minor_short_multiple_separation (k : ℕ) (P θ : ℝ)
    (hθ : θ∈Set.Ioc 0 1) (hminor : θ∉ordinaryBroadMajor k P)
    (d : ℕ) (hd : 1≤d) (hdP : (d : ℝ)≤P) :
    broadArcWidth k P < integerDistance ((d : ℝ)*θ) := by
  by_contra h
  have herr : integerDistance ((d : ℝ)*θ)≤broadArcWidth k P := le_of_not_gt h
  have hmul0 : 0≤(d : ℝ)*θ := mul_nonneg (Nat.cast_nonneg _) hθ.1.le
  have hmuld : (d : ℝ)*θ≤d := by
    nlinarith [show (0 : ℝ)≤d from Nat.cast_nonneg d,hθ.2]
  have ha0 : 0≤round ((d : ℝ)*θ) := by
    simpa using round_monotone_real hmul0
  have had : round ((d : ℝ)*θ)≤d := by
    simpa using round_monotone_real hmuld
  apply hminor
  exact mem_periodicMajorRegion_of_unreduced (broadDenominators P)
    (broadArcWidth k P) θ hθ (round ((d : ℝ)*θ)) d (by omega) ha0 had
    (fun q hq=>(mem_broadDenominators P q).mpr
      ((show (q : ℝ)≤d by exact_mod_cast hq).trans hdP)) herr

/-- Uniform reciprocal averaging on the actual minor complement, with no
separate Diophantine hypothesis retained. -/
theorem ordinary_minor_reciprocal_average (k : ℕ) (hk : 2≤k)
    (L : ℝ) (hL : 1≤L) {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N → ∀ θ α : ℝ,
      θ∈Set.Ioc 0 1 → θ∉ordinaryBroadMajor k N →
      (N : ℝ)⁻¹*(∑ y∈Finset.Icc 1 N,
        FiniteSpacing.truncatedReciprocal ((L*(N : ℝ)^(k-1))⁻¹)
          (integerDistance ((k : ℝ)*y*θ+α)))≤C*(N : ℝ)^((k : ℝ)-2+ε) := by
  obtain ⟨C,hC,hbound⟩ := CriticalVMVTMinorSpacing.reciprocal_average_bound k hk L hL hε
  refine ⟨C,hC,?_⟩
  intro N hN θ α hθ hm
  exact hbound N hN θ α (fun d hd hdN=>ordinary_minor_short_multiple_separation
    k N θ hθ hm d hd (by exact_mod_cast hdN))

#print axioms ordinary_minor_short_multiple_separation
#print axioms ordinary_minor_reciprocal_average
end Waring.EndgameCompletion
