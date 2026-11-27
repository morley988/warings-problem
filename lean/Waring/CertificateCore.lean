import Std

/-!
Exact finite rational audit for the degree-eight and degree-nine recipes.
This module has no analytic assumptions and makes no assertion about Waring's G.
It defines the finite arithmetic rules, with all guards part of the checker.
All generated acceptance proofs use `decide +kernel`.
-/
namespace Waring.Certificate

abbrev Q := Rat
abbrev Curve := Array Q

def q (n : Nat) : Q := n

def qmin (x y : Q) : Q := if x ≤ y then x else y
def qmax (x y : Q) : Q := if x ≤ y then y else x

def sumQ (xs : Array Q) : Q := xs.toList.foldl (· + ·) 0

def minQ (xs : Array Q) : Option Q := do
  let first ← xs[0]?
  return xs.toList.foldl qmin first

def maxQ (xs : Array Q) : Option Q := do
  let first ← xs[0]?
  return xs.toList.foldl qmax first

structure InterpolatedCurve where
  values : Curve
  witnesses : Array (Nat × Nat)
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Every selected moment is a chord of two available moments in the same snapshot.
No assumption about numerical convex-hull optimization is used. -/
def checkInterpolationAt (raw : Curve) (c : InterpolatedCurve) (i : Nat) : Bool :=
  let (a, b) := c.witnesses[i]!
  let value := if a == b then raw[a]!
    else (q (b-i)*raw[a]! + q (i-a)*raw[b]!) / q (b-a)
  decide (a ≤ i) && decide (i ≤ b) && decide (b < raw.size) &&
    decide (c.values[i]! = value)

def checkInterpolation (raw : Curve) (c : InterpolatedCurve) : Bool :=
  decide (raw.size = c.values.size) && decide (raw.size = c.witnesses.size) &&
  (List.range raw.size).all (checkInterpolationAt raw c)

/-- Only even full moment orders occurring within the supplied finite tables. -/
def moment (c : Curve) (p : Nat) : Option Q := do
  if p % 2 != 0 then none else c[p/2]?

def delta (k : Nat) (c : Curve) (p : Nat) : Option Q := do
  let value ← moment c p
  return qmax 0 (value - q p + q k)

inductive ResourceKind where
  | z2 | z4 | z4Refined | basic | refined | cube
  deriving BEq, Repr, Inhabited, DecidableEq

structure Resource where
  kind : ResourceKind
  factor : Nat
  order : Nat
  weight : Q
  deriving BEq, Repr, Inhabited, DecidableEq

structure Piece where
  lo : Q
  hi : Q
  resources : Array Resource
  deriving BEq, Repr, Inhabited, DecidableEq

structure Policy where
  halfOrder : Nat
  path : Array Nat
  phi : Array Q
  auxiliaryOrder : Option Nat
  pieces : Array Piece
  deriving BEq, Repr, Inhabited, DecidableEq

structure Endpoint where
  height : Q
  saving : Q
  exponent : Q
  deriving BEq, Repr, Inhabited, DecidableEq

structure PieceResult where
  mass : Q
  loads : Array Q
  endpoints : Array Endpoint
  deriving BEq, Repr, Inhabited, DecidableEq

structure Backward where
  index : Nat
  diagonal : Q
  prefactor : Q
  output : Q
  deriving BEq, Repr, Inhabited, DecidableEq

structure Evaluation where
  major : Q
  prefixMargins : Array Q
  pieces : Array PieceResult
  backwards : Array Backward
  raw : Q
  deriving BEq, Repr, Inhabited, DecidableEq

/-- The six resource formulas used by the frozen certificates. -/
def resourceValue (k : Nat) (phi : Array Q) (height : Q)
    (coefficient : Curve) (r : Resource) : Option Q := do
  let total := sumQ phi
  let length := 1 - total
  let h := q k - 2 - q k * total
  if r.kind == .z2 then
    if r.factor != 0 || r.order != 2 then failure
    return 1
  if r.kind == .z4 then
    if r.factor != 0 || r.order != 4 then failure
    return qmin height (qmin 2 h)
  if r.kind == .z4Refined then
    if r.factor != 0 || r.order != 4 then failure
    return qmin (2*height-h) 2
  if r.factor == 0 || r.factor > phi.size || r.order < 2 then failure
  let f := phi[r.factor-1]!
  if r.kind == .basic then
    if r.order != 2 then failure
    let caps := if phi.size ≤ k-4 then #[f]
      else #[f, q k-6-q k*total+4*q k*f, length/4,
        (q k*length-(4*q k-1)*f)/6]
    let value ← minQ caps
    if value < 0 then failure
    return value
  let d ← delta (2*k) coefficient r.order
  let caps := #[2*q k*f, q k-3-q k*total+q k*f,
    (q k-6-q k*total+6*q k*f)/2]
  let value ← minQ caps
  if value < 0 then failure
  let cap := if r.kind == .refined then height-2+2*q k*f else height/3
  return qmin value cap - d*f

/-- Recompute one entire policy, including guards, height endpoints and counted
backward stages. All four policies of a round use the same `curve` argument. -/
def evaluate (k : Nat) (curve coefficient : Curve) (p : Policy) : Option Evaluation := do
  let j := p.phi.size
  let s := p.halfOrder
  if k < 4 || s < 2 || p.path.size != j || j < 1 || j > k-2 then failure
  if p.path[0]! != s-1 then failure
  for f in p.phi.toList do
    if f < 0 || 1 / q k < f then failure
  let mut totals : Array Q := #[0]
  let mut acc : Q := 0
  for f in p.phi.toList do
    acc := acc + f
    totals := totals.push acc
  let lengths := (totals.toList.map (fun t => 1-t)).toArray
  let shifts := ((List.range (j+1)).map (fun i => q i-q k*totals[i]!)).toArray
  let top := q k / 2 * lengths[j]!
  if top ≤ 1 then failure
  let amp := 1 + shifts[j]! + totals[j]!
  let r := p.path[j-1]!
  let v := p.auxiliaryOrder.getD (2*r)
  if v == 0 then failure
  let c := if p.auxiliaryOrder.isSome then q (2*r) / q v else 1
  let a := 1-c
  let gamma := 1-2*a
  let mut prefixMargins : Array Q := #[]
  if p.auxiliaryOrder.isSome then
    if j != k-2 || a < 0 || c < 0 || gamma < 0 then failure
    if a+c != 1 || gamma+2*a != 1 || c*q v != q (2*r) then failure
    for i in (List.range (j-1)).map (fun t => t+2) do
      let margin := 1 - totals[i]! - (q k-2)*p.phi[i-1]!
      if margin < 0 then failure
      prefixMargins := prefixMargins.push margin
  let base := (gamma+a)*amp + c*(q v-q k)*lengths[j]!
  let dv ← delta k curve v
  let dr ← delta k curve (2*r)
  let cn := 2/q k*c*dv
  let root := 1/q (2^(k-j-2))
  let major := amp+(q (2*r)-q k)*lengths[j]! + qmax 0 (2/q k*dr-1/q (k-j))
  let mut ends : Array Q := #[]
  let mut pieces : Array PieceResult := #[]
  let mut last : Q := 0
  for piece in p.pieces.toList do
    if piece.lo != last || piece.hi ≤ piece.lo || 1 < piece.hi then failure
    last := piece.hi
    let mut mass : Q := 0
    let mut loads : Array Q := Array.replicate (j+1) 0
    for res in piece.resources.toList do
      if res.weight ≤ 0 || res.factor > j then failure
      mass := mass + res.weight
      loads := loads.set! res.factor (loads[res.factor]! + q res.order*res.weight)
    if 1 < mass then failure
    for load in loads.toList do
      if load < 0 || 1 < load then failure
    let mut endpoints : Array Endpoint := #[]
    for t in [piece.lo,piece.hi] do
      let ell := 1+t*(top-1)
      let mut saving : Q := 0
      for res in piece.resources.toList do
        let value ← resourceValue k p.phi ell coefficient res
        saving := saving + res.weight*value
      let exponent := base+cn*ell-gamma*root*qmin 1 saving
      endpoints := endpoints.push ⟨ell,saving,exponent⟩
      ends := ends.push exponent
    pieces := pieces.push ⟨mass,loads,endpoints⟩
  if last != 1 then failure
  let mut current ← maxQ (#[major] ++ ends)
  let mut backwards : Array Backward := #[]
  for t in (List.range (j-1)).map (fun u => u+1) do
    let i := j-t
    let rr := p.path[i-1]!
    let u := p.path[i]!
    if u >= 2*rr then failure
    let h := 2*rr-u
    if h == 0 || h >= 2*rr then failure
    let lu ← moment curve (2*u)
    let lh ← moment curve (2*h)
    let diagonal := 1+shifts[i]!+totals[i+1]!+lu*lengths[i+1]!
    let prefactor := (lh*lengths[i]!+shifts[i]!+totals[i]!+(q (2*u)-1)*p.phi[i]!)/2
    current := prefactor + qmax diagonal current/2
    backwards := backwards.push ⟨i,diagonal,prefactor,current⟩
  let firstMoment ← moment curve (2*(s-1))
  let first := 1+p.phi[0]!+firstMoment*lengths[1]!
  let raw := (q (2*s)-3)*p.phi[0]!+qmax first current
  return ⟨major,prefixMargins,pieces,backwards,raw⟩

structure Entry where
  evaluation : Evaluation
  rounded : Q
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Exact upward rounding to the 10^-12 grid, stated without trusting a ceiling
algorithm. The strict lower inequality gives the unique grid point. -/
def checkRounding (raw rounded : Q) : Bool :=
  decide (raw ≤ rounded) && decide (rounded-1/1000000000000 < raw) &&
  ((rounded*1000000000000).den == 1)

def checkEntry (k : Nat) (curve coefficient : Curve) (policy : Policy) (entry : Entry) : Bool :=
  match evaluate k curve coefficient policy with
  | none => false
  | some result => decide (result = entry.evaluation) && checkRounding result.raw entry.rounded

structure Round where
  inputs : Curve
  interpolation : InterpolatedCurve
  entries : Array Entry
  outputs : Curve
  deriving BEq, Repr, Inhabited, DecidableEq

/-- One simultaneous round, including the exact preceding snapshot link and
all four policy checks. Entries never read another output from their own round. -/
def updatedCurve (policies : Array Policy) (round : Round) : Curve :=
  (List.range policies.size).foldl (fun outputs i =>
    let p := policies[i]!
    let e := round.entries[i]!
    outputs.set! p.halfOrder (qmin round.interpolation.values[p.halfOrder]! e.rounded))
    round.inputs

def checkRoundEntry (k : Nat) (policies : Array Policy) (coefficient : Curve)
    (round : Round) (i : Nat) : Bool :=
  decide (policies[i]!.halfOrder < round.inputs.size) &&
  checkEntry k round.interpolation.values coefficient policies[i]! round.entries[i]!

def checkRound (k : Nat) (policies : Array Policy) (coefficient : Curve)
    (previous : Curve) (round : Round) : Bool :=
  decide (round.inputs = previous) && checkInterpolation round.inputs round.interpolation &&
  decide (policies.size = round.entries.size) &&
  (List.range policies.size).all (checkRoundEntry k policies coefficient round) &&
  decide (updatedCurve policies round = round.outputs)

end Waring.Certificate
