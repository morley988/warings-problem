import WaringLimit.Words

/-! Exact limiting conductor coverage and integration charges.
Heights have scale T=10^32, moduli have scale B=10^6 and the
cumulative charge uses D=10^16. The records contain an A/B word
and a chain of at most three explicit Weyl intervals. -/
namespace WaringLimit
open WaringEnvelope (ceilDiv expLoopScale)

def T : Nat := 10^32
def B : Nat := 10^6
def D : Nat := 10^16
def F : Nat := 300
def z₀ : Nat := 107*T/1000
def retentionNum : Nat := 99999
def retentionDen : Nat := 100000

/-- A single log-charge upper bound for adjacent height levels,
with one extra integer comparison to cover floor rounding. -/
def hopLog : Nat := 9995003333334
def hopNum : Nat := 1001000000000000001
def hopDen : Nat := 10^18

structure State where
  z : Nat
  m : Nat
  cost : Nat
deriving Repr, DecidableEq

def start : State := ⟨z₀,B,0⟩

def weylChain : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, endpoint, code => if code=0 then some endpoint else none
  | fuel+1, σ, endpoint, code => do
    if code=0 then return endpoint
    let j := code%1024
    let t := min (2^(j-1)) (j*(j-1))*σ
    if !(2≤j && j≤2*F+1 && 2*t≤T && B*(j+1)*t≤endpoint*T) then none else
      let hi := B*min ((j+1)*(T-t)) (j*T-t)/T
      if endpoint<hi then weylChain fuel σ hi (code/1024) else none

def endpoint (z code : Nat) : Option Nat := do
  let e ← words[code%256]?
  let σ := ceilDiv (200001*z) 100000
  if !(0<z && 2*z<σ && e.den*σ ≤ (e.den-e.y)*T) then none else
    let p := B+B*((e.den-e.y)*T-e.den*σ)/(e.x*T)
    let q ← weylChain 3 σ p (code/256)
    return min (F*B) q

def step (s : State) (code : Nat) : Option State := do
  let m ← endpoint s.z code
  let z := s.z*1000/1001
  if !(s.m≤m && m<F*B && 0<z && z<s.z &&
       s.z*hopDen ≤ z*hopNum &&
       (s.z != z₀ || retentionNum*m*T > 2*(T-z₀)*retentionDen*B)) then none else
    let charge := ceilDiv (2*hopLog*B*retentionDen) (m*retentionNum)
    return ⟨z,m,s.cost+charge⟩

def scan : State → List Nat → Option State
  | s, [] => some s
  | s, c::cs => (step s c).bind (fun t => scan t cs)

inductive Path : State → State → Prop
  | refl : Path s s
  | snoc : Path s t → step t c = some u → Path s u

theorem Path.trans (h : Path s t) (k : Path t u) : Path s u := by
  induction k with
  | refl => exact h
  | snoc _ hstep ih => exact .snoc ih hstep

theorem path_of_scan (cs : List Nat) (s t : State) (h : scan s cs = some t) : Path s t := by
  induction cs generalizing s with
  | nil =>
    simp only [scan,Option.some.injEq] at h
    subst t
    exact .refl
  | cons c cs ih =>
    cases e : step s c with
    | none => simp [scan,e] at h
    | some u =>
      have hu : scan u cs = some t := by simpa [scan,e] using h
      exact (Path.snoc Path.refl e).trans (ih u hu)

/-- Floor evaluation of an exponential (at independent internal precision)
to prove that the proposed rational logarithm is large enough. -/
def validLog (p q h : Nat) : Bool :=
  let I := D^2
  0<p && 0<q && p*I ≤ q*expLoopScale I (h*D) 120 I

def baseLog : Nat := 21217577464145929
def plateauLog : Nat := 425802773535025

/-- The three inequalities for h=3/2, b=h+1/F, τ=1/14 in the continuous
tail (hence 2τ h b = 3n/(28F), with n=3F+2). -/
def tailOK : Bool :=
  let n := 3*F+2
  3*n*(3*F+4)*128*F+n*(3*F+4)*28*F < 2*F*128*F*28*F &&
  3*n*3 < 28*F &&
  3*n*128*F+n*28*F < 64*F^2*28*F

def finalCost (s : State) : Nat :=
  2*D+baseLog+s.cost+ceilDiv (2*plateauLog*retentionDen) (F*retentionNum)+
    ceilDiv (4*D*retentionDen) (F*retentionNum)

def certifiedEnd (s : State) (c bound : Nat) : Bool :=
  endpoint s.z c == some (F*B) && s.m≤F*B && T≤s.z*14*F^2 &&
    tailOK && validLog (T-z₀) z₀ baseLog &&
    validLog (s.z*F^2*14) T plateauLog && validLog hopNum hopDen hopLog &&
    finalCost s ≤ bound

def Certified (bound : Nat) : Prop :=
  words.all entryOK = true ∧ ∃ s, Path start s ∧ ∃ c, certifiedEnd s c bound = true

end WaringLimit
