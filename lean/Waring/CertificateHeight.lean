import Waring.CertificateGuards
import Waring.CertificateSoundness
import Waring.Height
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The certificate's real height functions

The definitions below use exactly the rational constants and cap arrays of
`resourceValue`. Successful resource evaluation commutes with the embedding
of the rationals into the reals. Nonnegative weighted resource savings are
concave, including the retained diagonal cap. Consequently exact rational
endpoint bounds control the residual at every real height of a piece.

These results concern the certificate formulas. The exponential-sum estimates
which justify treating each resource formula as an analytic saving remain
separate obligations.
-/

noncomputable section

namespace Waring.Certificate

def resourceSizeCap (k : Nat) (p : Policy) (r : Resource) : Q :=
  (minQ (resourceSizeCaps k p r)).getD 0

def resourceLoss (k : Nat) (p : Policy) (coefficient : Curve) (r : Resource) : Q :=
  (delta (2*k) coefficient r.order).getD 0 * p.phi[r.factor-1]!

/-- Total rational form of a resource; the defaults are irrelevant whenever
the guarded evaluator succeeds. -/
def resourceFormula (k : Nat) (p : Policy) (coefficient : Curve) (r : Resource)
    (height : Q) : Q :=
  match r.kind with
  | .z2 => 1
  | .z4 => qmin height (qmin 2 (heightExponent k p))
  | .z4Refined => qmin (2*height-heightExponent k p) 2
  | .basic => resourceSizeCap k p r
  | .refined => qmin (resourceSizeCap k p r)
      (height-2+2*q k*p.phi[r.factor-1]!) - resourceLoss k p coefficient r
  | .cube => qmin (resourceSizeCap k p r) (height/3) - resourceLoss k p coefficient r

/-- The real function with exactly the same static rational data. -/
def resourceReal (k : Nat) (p : Policy) (coefficient : Curve) (r : Resource)
    (height : ℝ) : ℝ :=
  match r.kind with
  | .z2 => 1
  | .z4 => min height (min 2 (heightExponent k p : ℝ))
  | .z4Refined => min (2*height-(heightExponent k p : ℝ)) 2
  | .basic => (resourceSizeCap k p r : ℝ)
  | .refined => min (resourceSizeCap k p r : ℝ)
      (height-2+(2*q k*p.phi[r.factor-1]! : Q)) - (resourceLoss k p coefficient r : ℝ)
  | .cube => min (resourceSizeCap k p r : ℝ) (height/3) - (resourceLoss k p coefficient r : ℝ)

theorem cast_qmin (a b : Q) : ((qmin a b : Q) : ℝ) = min (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · have h' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    simp [qmin, h]
  · have h' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast le_of_not_ge h
    simp [qmin, h, min_eq_right h']

theorem resourceFormula_cast (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) (height : Q) :
    (resourceFormula k p coefficient r height : ℝ) =
      resourceReal k p coefficient r (height : ℝ) := by
  cases h : r.kind <;>
    simp [resourceFormula, resourceReal, h, cast_qmin]

private theorem cap_affine_concave (cap a b loss : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => min cap (a*x+b)-loss) := by
  have hc := Height.min_concave (concaveOn_const cap convex_univ)
    (Height.affine_concave a b)
  simpa only [Pi.sub_apply] using hc.sub (convexOn_const loss convex_univ)

theorem resourceReal_concave (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) : ConcaveOn ℝ Set.univ (resourceReal k p coefficient r) := by
  change ConcaveOn ℝ Set.univ (fun x : ℝ => resourceReal k p coefficient r x)
  cases h : r.kind
  · simpa only [resourceReal, h] using
      (concaveOn_const (1 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)))
  · simpa only [resourceReal, h, min_assoc] using
      Height.quadratic_old_concave (heightExponent k p : ℝ)
  · simpa only [resourceReal, h, min_comm] using
      Height.quadratic_refined_concave (heightExponent k p : ℝ)
  · simpa only [resourceReal, h] using
      (concaveOn_const (resourceSizeCap k p r : ℝ)
        (convex_univ : Convex ℝ (Set.univ : Set ℝ)))
  · convert cap_affine_concave (resourceSizeCap k p r : ℝ) 1
      (-2+(2*q k*p.phi[r.factor-1]! : Q)) (resourceLoss k p coefficient r : ℝ) using 1
    simp only [resourceReal, h, one_mul, sub_eq_add_neg, add_assoc]
  · convert cap_affine_concave (resourceSizeCap k p r : ℝ) (1/3) 0
      (resourceLoss k p coefficient r : ℝ) using 1
    simp only [resourceReal, h, add_zero, div_eq_mul_inv, one_mul, mul_comm]

/-- No default value is used in this identity: it assumes that every guard of
the original resource evaluator succeeded. -/
theorem resourceValue_eq_formula (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) (height value : Q)
    (heval : resourceValue k p.phi height coefficient r = some value) :
    resourceFormula k p coefficient r height = value := by
  cases hk : r.kind <;>
    simp [resourceValue, hk, resourceFormula, resourceSizeCap,
      resourceSizeCaps, resourceLoss, heightExponent,
      instBEqResourceKind, instBEqResourceKind.beq, ResourceKind.ctorIdx] at heval ⊢
  all_goals try exact heval.2
  all_goals simp only [Option.bind_eq_some_iff] at heval
  case basic =>
    rcases heval.2.2 with ⟨cap, hcap, hv⟩
    rw [hcap, Option.getD_some]
    simpa using (show (¬cap < 0) ∧ cap = value by simpa using hv).2
  all_goals
    rcases heval.2 with ⟨d, hd, cap, hcap, hv⟩
    rw [hd, hcap, Option.getD_some, Option.getD_some]
    split_ifs at hv
    simp_all

theorem resourceValue_cast (k : Nat) (p : Policy) (coefficient : Curve)
    (r : Resource) (height value : Q)
    (heval : resourceValue k p.phi height coefficient r = some value) :
    resourceReal k p coefficient r (height : ℝ) = (value : ℝ) := by
  rw [← resourceFormula_cast, resourceValue_eq_formula k p coefficient r height value heval]

def savingFormulaList (k : Nat) (p : Policy) (coefficient : Curve)
    (height : Q) : List Resource → Q
  | [] => 0
  | r :: rs => r.weight*resourceFormula k p coefficient r height +
      savingFormulaList k p coefficient height rs

def savingRealList (k : Nat) (p : Policy) (coefficient : Curve)
    (height : ℝ) : List Resource → ℝ
  | [] => 0
  | r :: rs => (r.weight : ℝ)*resourceReal k p coefficient r height +
      savingRealList k p coefficient height rs

def pieceSavingFormula (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (height : Q) : Q :=
  savingFormulaList k p coefficient height piece.resources.toList

def pieceSavingReal (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (height : ℝ) : ℝ :=
  savingRealList k p coefficient height piece.resources.toList

theorem savingFormulaList_cast (k : Nat) (p : Policy) (coefficient : Curve)
    (height : Q) (resources : List Resource) :
    (savingFormulaList k p coefficient height resources : ℝ) =
      savingRealList k p coefficient (height : ℝ) resources := by
  induction resources with
  | nil => simp [savingFormulaList, savingRealList]
  | cons r rs ih => simp [savingFormulaList, savingRealList, resourceFormula_cast, ih]

theorem pieceSavingFormula_cast (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (height : Q) :
    (pieceSavingFormula k p coefficient piece height : ℝ) =
      pieceSavingReal k p coefficient piece (height : ℝ) :=
  savingFormulaList_cast k p coefficient height piece.resources.toList

theorem savingFormulaList_eq_foldl (k : Nat) (p : Policy) (coefficient : Curve)
    (height : Q) (resources : List Resource) (initial : Q) :
    resources.foldl (fun acc r => acc+r.weight*resourceFormula k p coefficient r height)
      initial = initial+savingFormulaList k p coefficient height resources := by
  induction resources generalizing initial with
  | nil => simp [savingFormulaList]
  | cons r rs ih =>
      simpa [List.foldl_cons, savingFormulaList, add_assoc] using
        (ih (initial+r.weight*resourceFormula k p coefficient r height))

theorem savingRealList_concave (k : Nat) (p : Policy) (coefficient : Curve)
    (resources : List Resource) (hw : ∀ r ∈ resources, 0 ≤ r.weight) :
    ConcaveOn ℝ Set.univ (fun x => savingRealList k p coefficient x resources) := by
  induction resources with
  | nil => simpa only [savingRealList] using
      (concaveOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set ℝ)))
  | cons r rs ih =>
    have hr : (0 : ℝ) ≤ (r.weight : ℝ) := by exact_mod_cast hw r (by simp)
    have hrs : ∀ t ∈ rs, 0 ≤ t.weight := fun t ht => hw t (by simp [ht])
    simpa only [savingRealList] using Height.weighted_add_concave
      (resourceReal_concave k p coefficient r) (ih hrs) hr

theorem pieceSavingReal_concave (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) :
    ConcaveOn ℝ Set.univ (pieceSavingReal k p coefficient piece) :=
  savingRealList_concave k p coefficient piece.resources.toList hw

/-- The diagonal cap used by the evaluator remains in the concavity theorem. -/
theorem capped_pieceSavingReal_concave (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) :
    ConcaveOn ℝ Set.univ (fun x => min (1 : ℝ) (pieceSavingReal k p coefficient piece x)) :=
  Height.diagonal_cap_concave (pieceSavingReal_concave k p coefficient piece hw)

def pieceResidualFormula (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (base slope scale height : Q) : Q :=
  base+slope*height-scale*qmin 1 (pieceSavingFormula k p coefficient piece height)

def pieceResidualReal (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (base slope scale : Q) : ℝ → ℝ :=
  Height.residual (base : ℝ) (slope : ℝ) (scale : ℝ)
    (pieceSavingReal k p coefficient piece)

theorem pieceResidualFormula_cast (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (base slope scale height : Q) :
    (pieceResidualFormula k p coefficient piece base slope scale height : ℝ) =
      pieceResidualReal k p coefficient piece base slope scale (height : ℝ) := by
  simp [pieceResidualFormula, pieceResidualReal, Height.residual,
    cast_qmin, pieceSavingFormula_cast]

theorem pieceResidualReal_convex (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (base slope scale : Q)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) (hscale : 0 ≤ scale) :
    ConvexOn ℝ Set.univ (pieceResidualReal k p coefficient piece base slope scale) := by
  apply Height.residual_convex (pieceSavingReal_concave k p coefficient piece hw)
  exact_mod_cast hscale

/-- Rational endpoint inequalities certify every real height in a piece. -/
theorem pieceResidualReal_le_of_rational_endpoints
    (k : Nat) (p : Policy) (coefficient : Curve) (piece : Piece)
    (base slope scale lo hi bound : Q) (height : ℝ)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) (hscale : 0 ≤ scale)
    (hheight : height ∈ Set.Icc (lo : ℝ) (hi : ℝ))
    (hlo : pieceResidualFormula k p coefficient piece base slope scale lo ≤ bound)
    (hhi : pieceResidualFormula k p coefficient piece base slope scale hi ≤ bound) :
    pieceResidualReal k p coefficient piece base slope scale height ≤ (bound : ℝ) := by
  apply Height.residual_le_of_endpoints
    (pieceSavingReal_concave k p coefficient piece hw) (by exact_mod_cast hscale) hheight
  · change pieceResidualReal k p coefficient piece base slope scale (lo : ℝ) ≤ (bound : ℝ)
    rw [← pieceResidualFormula_cast]
    exact_mod_cast hlo
  · change pieceResidualReal k p coefficient piece base slope scale (hi : ℝ) ≤ (bound : ℝ)
    rw [← pieceResidualFormula_cast]
    exact_mod_cast hhi

theorem policyGuards_weights_nonneg (k : Nat) (p : Policy)
    (hguard : PolicyAnalyticGuards k p) (piece : Piece) (hp : piece ∈ p.pieces.toList) :
    ∀ r ∈ piece.resources.toList, 0 ≤ r.weight := by
  intro r hr
  exact ((hguard.2.2.2.1 piece hp).2.2 r hr).1.le

/-- The normalized piece coordinate used verbatim by `evaluate`. -/
def normalizedHeight (top t : Q) : Q := 1+t*(top-1)

theorem normalizedHeight_cast (top t : Q) :
    (normalizedHeight top t : ℝ) = 1+(t : ℝ)*((top : ℝ)-1) := by
  simp [normalizedHeight]

theorem pieceResidualReal_le_of_normalized_endpoints
    (k : Nat) (p : Policy) (coefficient : Curve) (piece : Piece)
    (base slope scale top bound : Q) (t : ℝ)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight) (hscale : 0 ≤ scale)
    (htop : 1 ≤ top) (ht : t ∈ Set.Icc (piece.lo : ℝ) (piece.hi : ℝ))
    (hlo : pieceResidualFormula k p coefficient piece base slope scale
      (normalizedHeight top piece.lo) ≤ bound)
    (hhi : pieceResidualFormula k p coefficient piece base slope scale
      (normalizedHeight top piece.hi) ≤ bound) :
    pieceResidualReal k p coefficient piece base slope scale
      (1+t*((top : ℝ)-1)) ≤ (bound : ℝ) := by
  apply pieceResidualReal_le_of_rational_endpoints k p coefficient piece
    base slope scale (normalizedHeight top piece.lo) (normalizedHeight top piece.hi)
    bound _ hw hscale _ hlo hhi
  rw [normalizedHeight_cast, normalizedHeight_cast]
  have htop' : (1 : ℝ) ≤ (top : ℝ) := by exact_mod_cast htop
  constructor <;> nlinarith [ht.1, ht.2]

theorem guarded_pieceResidualReal_le_of_normalized_endpoints
    (k : Nat) (p : Policy) (coefficient : Curve) (piece : Piece)
    (hguard : PolicyAnalyticGuards k p) (hp : piece ∈ p.pieces.toList)
    (base slope scale top bound : Q) (t : ℝ) (hscale : 0 ≤ scale)
    (htop : 1 ≤ top) (ht : t ∈ Set.Icc (piece.lo : ℝ) (piece.hi : ℝ))
    (hlo : pieceResidualFormula k p coefficient piece base slope scale
      (normalizedHeight top piece.lo) ≤ bound)
    (hhi : pieceResidualFormula k p coefficient piece base slope scale
      (normalizedHeight top piece.hi) ≤ bound) :
    pieceResidualReal k p coefficient piece base slope scale
      (1+t*((top : ℝ)-1)) ≤ (bound : ℝ) :=
  pieceResidualReal_le_of_normalized_endpoints k p coefficient piece
    base slope scale top bound t (policyGuards_weights_nonneg k p hguard piece hp)
    hscale htop ht hlo hhi

/-- Recursive guarded summation of the same resource values used in the
evaluator's accumulator loop. -/
def savingValueList (k : Nat) (p : Policy) (coefficient : Curve) (height : Q) :
    List Resource → Option Q
  | [] => some 0
  | r :: rs => do
      let value ← resourceValue k p.phi height coefficient r
      let rest ← savingValueList k p coefficient height rs
      return r.weight*value+rest

theorem savingValueList_eq_formula (k : Nat) (p : Policy) (coefficient : Curve)
    (height : Q) (resources : List Resource) (value : Q)
    (heval : savingValueList k p coefficient height resources = some value) :
    savingFormulaList k p coefficient height resources = value := by
  induction resources generalizing value with
  | nil => simpa [savingValueList, savingFormulaList] using heval
  | cons r rs ih =>
    simp [savingValueList, Option.bind_eq_some_iff] at heval
    rcases heval with ⟨v, hv, rest, hrest, heq⟩
    rw [savingFormulaList, resourceValue_eq_formula k p coefficient r height v hv,
      ih rest hrest]
    exact heq

theorem savingValueList_cast (k : Nat) (p : Policy) (coefficient : Curve)
    (height : Q) (resources : List Resource) (value : Q)
    (heval : savingValueList k p coefficient height resources = some value) :
    savingRealList k p coefficient (height : ℝ) resources = (value : ℝ) := by
  rw [← savingFormulaList_cast, savingValueList_eq_formula k p coefficient height
    resources value heval]

structure TerminalParameters where
  top : Q
  base : Q
  slope : Q
  scale : Q
  deriving DecidableEq, Inhabited

/-- The terminal parameters of `evaluate`, using the last prefix sum as the
total of the `phi` array. Concrete associations below also check them directly
against every stored endpoint. -/
def terminalParameters (k : Nat) (curve : Curve) (p : Policy) : TerminalParameters :=
  let j := p.phi.size
  let total := sumQ p.phi
  let length := 1-total
  let amp := 1+(q j-q k*total)+total
  let r := p.path[j-1]!
  let v := p.auxiliaryOrder.getD (2*r)
  let c := if p.auxiliaryOrder.isSome then q (2*r)/q v else 1
  let a := 1-c
  let gamma := 1-2*a
  let dv := (delta k curve v).getD 0
  ⟨q k/2*length, (gamma+a)*amp+c*(q v-q k)*length,
    2/q k*c*dv, gamma*(1/q (2^(k-j-2)))⟩

def EndpointHeightAssociation (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (params : TerminalParameters) (t : Q) (endpoint : Endpoint) : Prop :=
  endpoint.height = normalizedHeight params.top t ∧
  savingValueList k p coefficient endpoint.height piece.resources.toList = some endpoint.saving ∧
  endpoint.exponent = params.base+params.slope*endpoint.height -
    params.scale*qmin 1 endpoint.saving

instance (k : Nat) (p : Policy) (coefficient : Curve) (piece : Piece)
    (params : TerminalParameters) (t : Q) (endpoint : Endpoint) :
    Decidable (EndpointHeightAssociation k p coefficient piece params t endpoint) := by
  unfold EndpointHeightAssociation
  infer_instance

def PieceHeightAssociation (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (params : TerminalParameters) (result : PieceResult) : Prop :=
  result.endpoints.size = 2 ∧
  EndpointHeightAssociation k p coefficient piece params piece.lo result.endpoints[0]! ∧
  EndpointHeightAssociation k p coefficient piece params piece.hi result.endpoints[1]!

instance (k : Nat) (p : Policy) (coefficient : Curve) (piece : Piece)
    (params : TerminalParameters) (result : PieceResult) :
    Decidable (PieceHeightAssociation k p coefficient piece params result) := by
  unfold PieceHeightAssociation
  infer_instance

def PolicyHeightAssociation (k : Nat) (curve coefficient : Curve)
    (p : Policy) (ev : Evaluation) : Prop :=
  1 ≤ (terminalParameters k curve p).top ∧
  0 ≤ (terminalParameters k curve p).scale ∧
  ev.pieces.size = p.pieces.size ∧
  ∀ i : Fin p.pieces.size,
    PieceHeightAssociation k p coefficient p.pieces[i.val]!
      (terminalParameters k curve p) ev.pieces[i.val]!

instance (k : Nat) (curve coefficient : Curve) (p : Policy) (ev : Evaluation) :
    Decidable (PolicyHeightAssociation k curve coefficient p ev) := by
  unfold PolicyHeightAssociation
  infer_instance

def RoundHeightAssociation (k : Nat) (policies : Array Policy) (coefficient : Curve)
    (round : Round) : Prop :=
  policies.size = round.entries.size ∧
  ∀ i : Fin policies.size,
    PolicyHeightAssociation k round.interpolation.values coefficient
      policies[i.val]! round.entries[i.val]!.evaluation

instance (k : Nat) (policies : Array Policy) (coefficient : Curve) (round : Round) :
    Decidable (RoundHeightAssociation k policies coefficient round) := by
  unfold RoundHeightAssociation
  infer_instance

theorem endpointHeightAssociation_eq (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (params : TerminalParameters) (t : Q) (endpoint : Endpoint)
    (h : EndpointHeightAssociation k p coefficient piece params t endpoint) :
    pieceResidualFormula k p coefficient piece params.base params.slope params.scale
      (normalizedHeight params.top t) = endpoint.exponent := by
  rw [← h.1]
  unfold pieceResidualFormula pieceSavingFormula
  rw [savingValueList_eq_formula k p coefficient endpoint.height piece.resources.toList
    endpoint.saving h.2.1]
  exact h.2.2.symm

/-- A checked endpoint association bounds every real point of its normalized
piece by the maximum of the two stored endpoint exponents. -/
theorem pieceHeightAssociation_all_heights (k : Nat) (p : Policy) (coefficient : Curve)
    (piece : Piece) (params : TerminalParameters) (result : PieceResult)
    (h : PieceHeightAssociation k p coefficient piece params result)
    (hw : ∀ r ∈ piece.resources.toList, 0 ≤ r.weight)
    (hscale : 0 ≤ params.scale) (htop : 1 ≤ params.top) (t : ℝ)
    (ht : t ∈ Set.Icc (piece.lo : ℝ) (piece.hi : ℝ)) :
    pieceResidualReal k p coefficient piece params.base params.slope params.scale
      (1+t*((params.top : ℝ)-1)) ≤
        max (result.endpoints[0]!.exponent : ℝ) (result.endpoints[1]!.exponent : ℝ) := by
  have hb := pieceResidualReal_le_of_normalized_endpoints k p coefficient piece
    params.base params.slope params.scale params.top
    (qmax result.endpoints[0]!.exponent result.endpoints[1]!.exponent) t hw hscale htop ht
  have hlo := endpointHeightAssociation_eq k p coefficient piece params piece.lo
    result.endpoints[0]! h.2.1
  have hhi := endpointHeightAssociation_eq k p coefficient piece params piece.hi
    result.endpoints[1]! h.2.2
  have hmax (a b : Q) : (qmax a b : ℝ) = max (a : ℝ) (b : ℝ) := by
    by_cases hab : a ≤ b
    · have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      simp [qmax, hab]
    · have hab' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast le_of_not_ge hab
      simp [qmax, hab, max_eq_left hab']
  rw [← hmax]
  apply hb
  · rw [hlo]
    unfold qmax
    split_ifs with hab
    · exact hab
    · exact le_rfl
  · rw [hhi]
    unfold qmax
    split_ifs with hab
    · exact le_rfl
    · exact le_of_not_ge hab

end Waring.Certificate
