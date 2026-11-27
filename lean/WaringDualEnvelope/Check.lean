import WaringDualEnvelope.Bank

/-! # Exact finite and infinite menus with arithmetic exponent pairs -/
namespace WaringDualEnvelope
open WaringEnvelope

structure Config extends WaringEnvelope.Config where
  heightTop : Nat
deriving DecidableEq, Repr

def configOK (c : Config) : Bool :=
  let base := c.first
  let endp := if c.last=0 then base else c.last
  21 ≤ base && base ≤ endp && c.root^2 ≤ base && base < (c.root+1)^2 &&
  0 < c.heightTop && c.heightTop < T &&
  validLog (T-c.heightTop) c.heightTop c.baseLog && validLog endp 1 c.endLog

/-- The minimum of the exponent-pair saving occurs at the right endpoint
of its conductor interval. All terms are compared after clearing denominators. -/
def pairAdmits (c : Config) (m sig : Nat) (p : Pair) : Bool :=
  let (h,v) := if c.last=0 then (1,8*c.root) else (m,B*c.first)
  let d := p.denominator
  let l := p.lossDen
  0 < d && 0 < l && 0 < v &&
    sig*d*B*l*v + T*(p.y*B*l*v + p.x*m*l*v + (p.loss+l)*d*B*h)
      ≤ T*(d+p.x)*B*l*v

def conductorTest (c : Config) (m sig code : Nat) : Bool :=
  if code < 2^130 then WaringEnvelope.chain c.toConfig m sig 16 B code else
    match pairBank[code-2^130]? with
    | none => false
    | some p => pairAdmits c m sig p.2

def row (c : Config) (s : State) (data : Nat) : Option State := do
  let z := data % (2^108)
  let rest := data / (2^108)
  let m := rest % (2^40)
  let proofCode := rest / (2^40)
  if !(0 < z && B ≤ m && m < B*c.first &&
       (c.last != 0 || m*8*c.root ≤ B*c.first) &&
       conductorTest c m (ceilDiv (20001*z) 10000) proofCode) then none else
  if s.modulus=0 then
    if z=c.heightTop && U*m*T > 2*(T-c.heightTop)*V*B then some ⟨z,m,0⟩ else none
  else if z<s.height && s.modulus ≤ m then
    some ⟨z,m,s.cost+intervalCost s.height z s.modulus⟩
  else none

def scan (c : Config) : State → List Nat → Option State
  | s,[] => some s
  | s,x::xs => (row c s x).bind (fun t => scan c t xs)

/-- A path carries a witness for every covered interval and each cost. -/
inductive Path (c : Config) : State → State → Prop
  | refl : Path c s s
  | extend : Path c s t → row c t x = some u → Path c s u

theorem Path.trans (h : Path c s t) (h' : Path c t u) : Path c s u := by
  induction h' with
  | refl => exact h
  | extend _ hrow ih => exact .extend ih hrow

theorem path_of_scan (c : Config) (xs : List Nat) (s t : State)
    (h : scan c s xs = some t) : Path c s t := by
  induction xs generalizing s with
  | nil =>
    simp only [scan, Option.some.injEq] at h
    subst t
    exact .refl
  | cons x xs ih =>
    cases e : row c s x with
    | none => simp [scan,e] at h
    | some u =>
      have hx : scan c u xs = some t := by simpa [scan,e] using h
      exact (Path.extend Path.refl e).trans (ih u hx)

def Certified (c : Config) (bound : Nat) : Prop :=
  configOK c = true ∧ ∃ s, Path c start s ∧
    (if c.last=0 then infiniteFinal c.toConfig s bound else finiteFinal c.toConfig s bound) = true

end WaringDualEnvelope
