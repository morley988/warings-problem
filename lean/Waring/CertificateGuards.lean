import Waring.CertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Waring.Certificate

/-- The quadratic product-height exponent H = P^h. -/
def heightExponent (k : Nat) (p : Policy) : Q := q k-2-q k*sumQ p.phi

def remainingLength (p : Policy) : Q := 1-sumQ p.phi

def resourceSizeCaps (k : Nat) (p : Policy) (r : Resource) : Array Q :=
  let total := sumQ p.phi
  let length := 1-total
  let f := p.phi[r.factor-1]!
  match r.kind with
  | .basic =>
    if p.phi.size ≤ k-4 then #[f]
    else #[f,q k-6-q k*total+4*q k*f,length/4,
      (q k*length-(4*q k-1)*f)/6]
  | .refined | .cube =>
    #[2*q k*f,q k-3-q k*total+q k*f,(q k-6-q k*total+6*q k*f)/2]
  | _ => #[]

def prefixMarginArray (k : Nat) (p : Policy) : Array Q :=
  ((List.range (p.phi.size-1)).map (fun t =>
    let i := t+2
    1-sumQ (p.phi.toList.take i).toArray-(q k-2)*p.phi[i-1]!)).toArray

def pieceMass (piece : Piece) : Q :=
  piece.resources.toList.foldl (fun acc r => acc+r.weight) 0

def pieceLoads (p : Policy) (piece : Piece) : Array Q :=
  piece.resources.toList.foldl (fun acc r =>
    acc.set! r.factor (acc[r.factor]!+q r.order*r.weight))
    (Array.replicate (p.phi.size+1) 0)

/-- Additional analytic range conditions, checked for the frozen policies.
These are stronger than the evaluator's non-strict guards. In particular h>1
is the missing global range premise needed by the sampled quadratic second
moment. -/
def PolicyAnalyticGuards (k : Nat) (p : Policy) : Prop :=
  1 < heightExponent k p ∧
  0 < remainingLength p ∧
  (∀ f ∈ p.phi.toList, 0 < f ∧ f < 1/q k) ∧
  (∀ piece ∈ p.pieces.toList,
    pieceMass piece < 1 ∧
    (∀ load ∈ (pieceLoads p piece).toList, load < 1) ∧
    (∀ res ∈ piece.resources.toList,
      0 < res.weight ∧ res.factor ≤ p.phi.size ∧
      ∀ cap ∈ (resourceSizeCaps k p res).toList, 0 < cap)) ∧
  (if p.auxiliaryOrder.isSome then
     ∀ margin ∈ (prefixMarginArray k p).toList, 0 < margin
   else True)

instance (k : Nat) (p : Policy) : Decidable (PolicyAnalyticGuards k p) := by
  unfold PolicyAnalyticGuards
  infer_instance

theorem policy8_0_guards : PolicyAnalyticGuards 8 policies8[0]! := by decide +kernel
theorem policy8_1_guards : PolicyAnalyticGuards 8 policies8[1]! := by decide +kernel
theorem policy8_2_guards : PolicyAnalyticGuards 8 policies8[2]! := by decide +kernel
theorem policy8_3_guards : PolicyAnalyticGuards 8 policies8[3]! := by decide +kernel
theorem policy9_0_guards : PolicyAnalyticGuards 9 policies9[0]! := by decide +kernel
theorem policy9_1_guards : PolicyAnalyticGuards 9 policies9[1]! := by decide +kernel
theorem policy9_2_guards : PolicyAnalyticGuards 9 policies9[2]! := by decide +kernel
theorem policy9_3_guards : PolicyAnalyticGuards 9 policies9[3]! := by decide +kernel

theorem auxiliary8_minimum_prefix_margin :
    minQ (prefixMarginArray 8 policies8[0]!) = some (9/20000000) := by decide +kernel

#print axioms policy8_0_guards
#print axioms policy9_3_guards
#print axioms auxiliary8_minimum_prefix_margin
end Waring.Certificate
