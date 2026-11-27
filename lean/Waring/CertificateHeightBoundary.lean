import Waring.CertificateHeightCoverage
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Extending the certified height interval to the actual minor-arc boundary

Every literal resource formula is globally Lipschitz with constant at most
2. The actual nonnegative certificate weights have total mass below one, so
the weighted saving and its diagonal cap inherit the same constant. Clamping
a height in [1-kappa,top] to the certified interval costs an explicit O(kappa)
error in both the resource savings and the complete terminal residual.
-/

noncomputable section
namespace Waring.Certificate

private theorem min_left_abs_bound (a x y : ℝ) :
    |min a x-min a y| ≤ |x-y| := by
  simpa using abs_min_sub_min_le_max a x a y

private theorem min_right_abs_bound (a x y : ℝ) :
    |min x a-min y a| ≤ |x-y| := by
  simpa only [min_comm] using min_left_abs_bound a x y

private theorem affine_abs_difference (a b x y : ℝ) :
    |(a*x+b)-(a*y+b)| = |a| *|x-y| := by
  have h : (a*x+b)-(a*y+b)=a*(x-y) := by ring
  rw [h,abs_mul]

def resourceHeightSlope : ResourceKind → ℝ
  | .z2 => 0
  | .z4 => 1
  | .z4Refined => 2
  | .basic => 0
  | .refined => 1
  | .cube => 1/3

theorem resourceHeightSlope_nonneg (kind : ResourceKind) : 0 ≤ resourceHeightSlope kind := by
  cases kind <;> norm_num [resourceHeightSlope]

theorem resourceHeightSlope_le_two (kind : ResourceKind) : resourceHeightSlope kind ≤ 2 := by
  cases kind <;> norm_num [resourceHeightSlope]

/-- The exact slope constants of all six literal resource formulas. -/
theorem resourceReal_abs_sub_le_slope (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) (x y : ℝ) :
    |resourceReal k p coefficient r x-resourceReal k p coefficient r y| ≤
      resourceHeightSlope r.kind*|x-y| := by
  cases hk : r.kind
  · simp [resourceReal,hk,resourceHeightSlope]
  · simpa only [resourceReal,hk,resourceHeightSlope,one_mul] using
      min_right_abs_bound (min 2 (heightExponent k p : ℝ)) x y
  · have h := min_right_abs_bound 2 (2*x-(heightExponent k p : ℝ))
      (2*y-(heightExponent k p : ℝ))
    have hid : |(2*x-(heightExponent k p : ℝ))-(2*y-(heightExponent k p : ℝ))| =
        2*|x-y| := by
      have heq : (2*x-(heightExponent k p : ℝ))-(2*y-(heightExponent k p : ℝ)) = 2*(x-y) := by ring
      rw [heq,abs_mul]
      norm_num
    simpa only [resourceReal,hk,resourceHeightSlope,hid] using h
  · simp [resourceReal,hk,resourceHeightSlope]
  · have h := min_left_abs_bound (resourceSizeCap k p r : ℝ)
      (x-2+(2*q k*p.phi[r.factor-1]! : Q))
      (y-2+(2*q k*p.phi[r.factor-1]! : Q))
    have hid : |(x-2+(2*q k*p.phi[r.factor-1]! : Q))-
        (y-2+(2*q k*p.phi[r.factor-1]! : Q))| = |x-y| := by congr 1; ring
    simp only [resourceReal,hk,resourceHeightSlope,one_mul]
    rw [sub_sub_sub_cancel_right]
    exact hid ▸ h
  · have h := min_left_abs_bound (resourceSizeCap k p r : ℝ) (x/3) (y/3)
    have hid : |x/3-y/3| = (1/3:ℝ)*|x-y| := by
      rw [← sub_div,abs_div]
      norm_num
      ring
    simp only [resourceReal,hk,resourceHeightSlope]
    rw [sub_sub_sub_cancel_right]
    exact hid ▸ h

/-- Every resource, including both quadratic branches, is 2-Lipschitz. -/
theorem resourceReal_abs_sub_le_two (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) (x y : ℝ) :
    |resourceReal k p coefficient r x-resourceReal k p coefficient r y| ≤ 2*|x-y| :=
  (resourceReal_abs_sub_le_slope k p coefficient r x y).trans
    (mul_le_mul_of_nonneg_right (resourceHeightSlope_le_two r.kind) (abs_nonneg _))

theorem resourceReal_lipschitz (k : Nat) (p : Policy) (coefficient : Curve) (r : Resource) :
    LipschitzWith 2 (resourceReal k p coefficient r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_ofNat] using resourceReal_abs_sub_le_two k p coefficient r x y

def resourceMassList : List Resource → ℝ
  | [] => 0
  | r :: rs => (r.weight : ℝ)+resourceMassList rs

theorem resourceMassList_eq_foldl (resources : List Resource) (initial : Q) :
    ((resources.foldl (fun acc r => acc+r.weight) initial : Q) : ℝ) =
      (initial : ℝ)+resourceMassList resources := by
  induction resources generalizing initial with
  | nil => simp [resourceMassList]
  | cons r rs ih =>
    simp only [List.foldl_cons,ih,resourceMassList,Rat.cast_add]
    ring

theorem pieceMass_cast (piece : Piece) :
    (pieceMass piece : ℝ) = resourceMassList piece.resources.toList := by
  simpa only [pieceMass,Rat.cast_zero,zero_add] using
    resourceMassList_eq_foldl piece.resources.toList 0

theorem savingRealList_abs_sub_le (k : Nat) (p : Policy) (coefficient : Curve)
    (resources : List Resource) (hw : ∀ r ∈ resources, 0 ≤ r.weight) (x y : ℝ) :
    |savingRealList k p coefficient x resources-savingRealList k p coefficient y resources| ≤
      2*resourceMassList resources*|x-y| := by
  induction resources with
  | nil => simp [savingRealList,resourceMassList]
  | cons r rs ih =>
    have hr : (0 : ℝ) ≤ (r.weight : ℝ) := by exact_mod_cast hw r (by simp)
    have hrest : ∀ t ∈ rs, 0 ≤ t.weight := fun t ht => hw t (by simp [ht])
    have hb := resourceReal_abs_sub_le_two k p coefficient r x y
    calc
      _ = |(r.weight : ℝ)*(resourceReal k p coefficient r x-resourceReal k p coefficient r y)+
          (savingRealList k p coefficient x rs-savingRealList k p coefficient y rs)| := by
        simp only [savingRealList]
        congr 1
        ring
      _ ≤ |(r.weight : ℝ)*(resourceReal k p coefficient r x-resourceReal k p coefficient r y)|+
          |savingRealList k p coefficient x rs-savingRealList k p coefficient y rs| := abs_add_le _ _
      _ = (r.weight : ℝ)*|resourceReal k p coefficient r x-resourceReal k p coefficient r y|+
          |savingRealList k p coefficient x rs-savingRealList k p coefficient y rs| := by
        rw [abs_mul,abs_of_nonneg hr]
      _ ≤ (r.weight : ℝ)*(2*|x-y|)+2*resourceMassList rs*|x-y| :=
        add_le_add (mul_le_mul_of_nonneg_left hb hr) (ih hrest)
      _ = _ := by simp only [resourceMassList]; ring

/-- The mass of the actual certificate piece, rather than its resource count,
controls the Lipschitz constant. -/
theorem pieceSavingReal_abs_sub_le_two (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight)
    (hmass : pieceMass piece ≤ 1) (x y : ℝ) :
    |pieceSavingReal k p coefficient piece x-pieceSavingReal k p coefficient piece y| ≤ 2*|x-y| := by
  have hm : resourceMassList piece.resources.toList ≤ 1 := by
    rw [← pieceMass_cast]
    exact_mod_cast hmass
  have hb := savingRealList_abs_sub_le k p coefficient piece.resources.toList hw x y
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ 2*|x-y| by positivity)
  nlinarith only [hh]

theorem capped_pieceSavingReal_abs_sub_le_two (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight)
    (hmass : pieceMass piece ≤ 1) (x y : ℝ) :
    |min 1 (pieceSavingReal k p coefficient piece x)-min 1 (pieceSavingReal k p coefficient piece y)| ≤
      2*|x-y| :=
  (min_left_abs_bound 1 _ _).trans
    (pieceSavingReal_abs_sub_le_two k p coefficient piece hw hmass x y)

/-- Absolute residual control is valid even without sign assumptions on its
linear slope or scale. -/
theorem pieceResidualReal_abs_sub_le (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (base slope scale : Q)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) (hmass : pieceMass piece ≤ 1)
    (x y : ℝ) :
    |pieceResidualReal k p coefficient piece base slope scale x-
      pieceResidualReal k p coefficient piece base slope scale y| ≤
      (|(slope : ℝ)|+2*|(scale : ℝ)|)*|x-y| := by
  have hb := capped_pieceSavingReal_abs_sub_le_two k p coefficient piece hw hmass x y
  calc
    _ = |(slope : ℝ)*(x-y)-(scale : ℝ)*
        (min 1 (pieceSavingReal k p coefficient piece x)-
          min 1 (pieceSavingReal k p coefficient piece y))| := by
      simp only [pieceResidualReal,Height.residual]
      congr 1
      ring
    _ ≤ |(slope : ℝ)*(x-y)|+|(scale : ℝ)*
        (min 1 (pieceSavingReal k p coefficient piece x)-
          min 1 (pieceSavingReal k p coefficient piece y))| := abs_sub _ _
    _ = |(slope : ℝ)| *|x-y|+|(scale : ℝ)| *
        |min 1 (pieceSavingReal k p coefficient piece x)-
          min 1 (pieceSavingReal k p coefficient piece y)| := by rw [abs_mul,abs_mul]
    _ ≤ |(slope : ℝ)| *|x-y|+|(scale : ℝ)| *(2*|x-y|) :=
      add_le_add_left (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) _
    _ = _ := by ring

/-- The clamped certified height; no exact minor-height threshold is assumed. -/
def certifiedHeight (top x κ : ℝ) : ℝ := min top (max 1 (x+κ))

theorem certifiedHeight_bounds {top x κ : ℝ} (htop : 1 ≤ top) (hκ : 0 ≤ κ)
    (hlo : 1-κ ≤ x) (hhi : x ≤ top) :
    certifiedHeight top x κ ∈ Set.Icc 1 top ∧ x ≤ certifiedHeight top x κ ∧
      certifiedHeight top x κ ≤ x+κ := by
  have hx : 1 ≤ x+κ := by linarith
  simp only [certifiedHeight,max_eq_right hx]
  exact ⟨⟨le_min htop hx,min_le_left _ _⟩,le_min hhi (by linarith),min_le_right _ _⟩

theorem certifiedHeight_distance {top x κ : ℝ} (htop : 1 ≤ top) (hκ : 0 ≤ κ)
    (hlo : 1-κ ≤ x) (hhi : x ≤ top) : |x-certifiedHeight top x κ| ≤ κ := by
  obtain ⟨_,hxy,hyx⟩ := certifiedHeight_bounds htop hκ hlo hhi
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  linarith

theorem resourceReal_clamped_lower (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) {top x κ : ℝ} (htop : 1 ≤ top) (hκ : 0 ≤ κ)
    (hlo : 1-κ ≤ x) (hhi : x ≤ top) :
    resourceReal k p coefficient r (certifiedHeight top x κ)-2*κ ≤
      resourceReal k p coefficient r x := by
  have hb := resourceReal_abs_sub_le_two k p coefficient r x (certifiedHeight top x κ)
  have hd := certifiedHeight_distance htop hκ hlo hhi
  have ha := (abs_le.mp hb).1
  linarith

/-- A certificate endpoint bound at the clamped height incurs only the
explicit Lipschitz error at the original height. -/
theorem pieceResidualReal_clamped_upper (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (base slope scale : Q)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) (hmass : pieceMass piece ≤ 1)
    {top x κ bound : ℝ} (htop : 1 ≤ top) (hκ : 0 ≤ κ)
    (hlo : 1-κ ≤ x) (hhi : x ≤ top)
    (hbound : pieceResidualReal k p coefficient piece base slope scale
      (certifiedHeight top x κ) ≤ bound) :
    pieceResidualReal k p coefficient piece base slope scale x ≤
      bound+(|(slope : ℝ)|+2*|(scale : ℝ)|)*κ := by
  have hb := pieceResidualReal_abs_sub_le k p coefficient piece base slope scale hw hmass
    x (certifiedHeight top x κ)
  have hd := certifiedHeight_distance htop hκ hlo hhi
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ |(slope : ℝ)|+2*|(scale : ℝ)| by positivity)
  have ha := (le_abs_self _).trans (hb.trans hm)
  linarith

#print axioms resourceReal_abs_sub_le_slope
#print axioms resourceReal_lipschitz
#print axioms pieceSavingReal_abs_sub_le_two
#print axioms pieceResidualReal_clamped_upper
end Waring.Certificate
