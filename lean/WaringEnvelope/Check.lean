import Std

/-! # Exact arithmetic for the scalar large-values menus
All heights use scale T, conductors use B, and the final cost uses D. Each
interval certificate gives a chain of explicit Weyl or differencing cells.
-/
namespace WaringEnvelope

def B : Nat := 10000
def T : Nat := 10^32
def D : Nat := 10^13
def U : Nat := 99999
def V : Nat := 100000
def F : Nat := 120
def top : Nat := 9985*T/100000

def ceilDiv (a b : Nat) := (a+b-1)/b

structure Config where
  first : Nat
  last : Nat  -- zero denotes the infinite band
  root : Nat
  baseLog : Nat
  endLog : Nat
  plateauLog : Nat
  capLog : Nat
deriving DecidableEq, Repr

structure State where
  height : Nat
  modulus : Nat
  cost : Nat
deriving DecidableEq, Repr

def start : State := ⟨0,0,0⟩

/-- Floor-Horner lower bound for a truncated exponential, in units of D. -/
def expLoopScale (d h n v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) id
    (fun i prev w => prev (d + h*w/(d*(i+1)))) n v

def expLoop := expLoopScale D

def validLog (num den h : Nat) : Bool :=
  0 < den && 0 < num && num*D ≤ den*expLoop h 120 D

def configOK (c : Config) : Bool :=
  let base := c.first
  let endp := if c.last=0 then base else c.last
  21 ≤ base && base ≤ endp && c.root^2 ≤ base && base < (c.root+1)^2 &&
  validLog (T-top) top c.baseLog && validLog endp 1 c.endLog

def slopes : Nat → Nat × Nat
  | 0 => (3,2)
  | 1 => (7,5)
  | 2 => (4,3)
  | 3 => (5,4)
  | 4 => (6,5)
  | 5 => (11,10)
  | _ => (21,20)

/-- Direct Weyl covering of the continuous conductor tail U'≥F. -/
def tailCell (K m sig p idx : Nat) : Bool :=
  let (e,f) := slopes idx
  let n := e*F+f
  let lhs := sig*e*n*m^2
  let den := T*f^2*F*B^2
  F*B ≤ p && e*m+f*B ≤ f*B*K &&
    lhs*(e*F+2*f)*f*F*B^2*K + n*m^2*(e*F+2*f)*den ≤ f^2*F^2*B^2*K*den &&
    lhs*e*B*K + e*m*den ≤ (e-f)*B*K*den &&
    lhs*f*F*B^2*K + n*m^2*den ≤ (e-f)*F^2*B^2*K*den

/-- One certified interval. The current continuous coverage is [B,p] in
scale B. The next interval has lower endpoint ≤p and returns its upper end. -/
def nextEndpoint (c : Config) (m sig p token : Nat) : Option Nat := do
  let K := c.first
  let (h, den) := if c.last=0 then (1,8*c.root) else (m,B*K)
  let common := T*den
  if token ≤ 41 then
    let j := token-1
    let y := 2^j*sig
    if !(1 ≤ token && j+2 ≤ K && 2*y ≤ T &&
      (j=0 || h*T ≤ den*(T-y)) &&
      B*(j*h*T+2*y*den) ≤ p*common) then none else
      some (B*((j+2)*T-(4*y-2*sig))/T)
  else if token ≤ 240 then
    let j := token-40
    let t := min (2^(j-1)) (j*(j-1))*sig
    if !(2 ≤ j && j ≤ K && 2*t ≤ T &&
      B*(j+1)*(t*den+j*h*T) ≤ p*common) then none else
      some (B*(min ((j+1)*(common-h*T-t*den)) (j*common-j*h*T-t*den))/common)
  else if token ≤ 247 && c.last != 0 && tailCell K m sig p (token-241) then
    some m
  else none

def chain (c : Config) (m sig : Nat) : Nat → Nat → Nat → Bool
  | 0,p,code => code=0 && m ≤ p
  | fuel+1,p,code =>
    if code=0 then m ≤ p else
    match nextEndpoint c m sig p (code%256) with
    | none => false
    | some q => p < q && chain c m sig fuel q (code/256)

/-- Upper bound on twice log(z/z') divided by retained conductor, using
2 log(x) ≤ x-1/x for x≥1 and outward integer rounding. -/
def intervalCost (z z' m : Nat) : Nat :=
  ceilDiv (D*(z^2-z'^2)*B*V) (z*z'*U*m)

def row (c : Config) (s : State) (data : Nat) : Option State := do
  let z := data % (2^108)
  let rest := data / (2^108)
  let m := rest % (2^40)
  let proofCode := rest / (2^40)
  if !(0 < z && B ≤ m && m < B*c.first &&
       (c.last != 0 || m*8*c.root ≤ B*c.first) &&
       chain c m (ceilDiv (20001*z) 10000) 16 B proofCode) then none else
  if s.modulus=0 then
    if z=top && U*m*T > 2*(T-top)*V*B then some ⟨z,m,0⟩ else none
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

/-- Price of the finite terminal branch, including variable rounding. -/
def finiteFinal (c : Config) (s : State) (bound : Nat) : Bool :=
  let (a,b) := if 7*(10*c.root) ≤ 20*21 then (7,20) else (21,10*c.root)
  c.last != 0 && 0 < s.modulus && 0 < b &&
    2*s.height*B*V*b*c.last*(10*c.endLog+81*D) <
      a*10*D*T*U*s.modulus &&
    2*D + c.baseLog + s.cost + ceilDiv (a*D) b + ceilDiv (6*D) c.first <
      bound + (2*D*B*V)/(U*s.modulus)

/-- The unbounded Weyl interval with h=3/2, tau=1/14 and H=sqrt(k)/8.
All three positive slack conditions are checked by cross multiplication. -/
def infiniteWeyl (r : Nat) : Bool :=
  let n := 3*F+2
  -- lhs = 2*(1/14)*(3/2)*(3/2+1/F) = 3*n/(28*F).
  3*n*(3*F+4)*128*F + n*(3*F+4)*28*F < 2*F*128*F*28*F &&
  3*n*24*r + 3*28*F < 8*r*28*F &&
  3*n*128*F + n*28*F < (64*F^2)*28*F

def infiniteFinal (c : Config) (s : State) (bound : Nat) : Bool :=
  let r := c.root
  let plateau := ceilDiv (2*c.plateauLog*V) (F*U)
  let tail := ceilDiv (4*D*V) (F*U)
  let asym := 2*D+c.baseLog+s.cost+plateau+tail
  let xN := 64*V*(10*c.endLog+81*D)
  let xD := 14*U*10*D
  c.last=0 && c.first=r^2 && 10^8 ≤ c.first && s.modulus=F*B &&
    T ≤ s.height*14*F^2 && infiniteWeyl r &&
    validLog (s.height*14*F^2) T c.plateauLog &&
    8*xD < xN && validLog xN xD c.capLog &&
    asym + ceilDiv (16*c.capLog*V) (r*U) + ceilDiv (16*D) r +
      ceilDiv (6*D) c.first < bound

def Certified (c : Config) (bound : Nat) : Prop :=
  configOK c = true ∧ ∃ s, Path c start s ∧
    (if c.last=0 then infiniteFinal c s bound else finiteFinal c s bound) = true

end WaringEnvelope
