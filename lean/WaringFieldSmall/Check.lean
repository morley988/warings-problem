import Std

/-! # Integer schedules for the sixth-through-higher field moment iteration

One interval [lo,hi] is checked together. The old ED starting excess and
all divisors are evaluated at the adverse endpoint. The slope cap uses
the other endpoint. Each action token stores a height, a modulus, and
a run length; all defects are upper bounds, in units of scale. -/
namespace WaringFieldSmall
def scale : Nat := 10^9
def modulusScale : Nat := 10000
def thetaNum : Nat := 99999
def thetaDen : Nat := 100000
def digit : Nat := 2^32
def modulusDigit : Nat := 2^24

structure Run where
  gain : Nat
  modulus : Nat
  steps : Nat

def unpack (n : Nat) : Run := ⟨n%digit, n/digit%modulusDigit, n/digit/modulusDigit⟩

def edRound (hi cap d : Nat) : Nat := d-(2*d*scale*(cap-1))/((hi*scale+d)*cap)

def fibreRound (hi : Nat) (s : Run) (d : Nat) : Nat :=
  d-min s.gain (d*thetaNum*s.modulus/(hi*thetaDen*modulusScale))

def repeats (f : Nat → Nat) : Nat → Nat → Nat
  | 0,x => x
  | n+1,x => repeats f n (f x)

structure State where
  order : Nat
  defect : Nat
  deriving DecidableEq, Repr

def start (lo hi j : Nat) : State :=
  ⟨2*(j+1), repeats (edRound hi (2^(min lo 32))) j ((hi-1)*scale)⟩

def advance (hi : Nat) (s : State) (data : Nat) : State :=
  let a := unpack data
  ⟨s.order+2*a.steps,repeats (fibreRound hi a) a.steps s.defect⟩

/-- The terminal threshold is strict. The arithmetical saving exponent
at degree k is 1/(15k) on a-1 marked factors. -/
def checked (lo hi j a : Nat) (data : List Nat) : Bool :=
  let s₀ := start lo hi j
  let s := data.foldl (advance hi) s₀
  11≤lo && lo≤hi && hi≤s₀.order && 1≤a && a%2=0 &&
  1000*(s.order+a+1)<6873*lo && 2*hi<s.order+a &&
  15*hi*s.defect<(a-1)*scale

/-- A band keeps both its verified numeric inequalities and its actual
row list, so the estimator can apply an analytic rule at each modulus. -/
structure Schedule where
  lo : Nat
  hi : Nat
  edIndex : Nat
  extra : Nat
  data : List Nat

abbrev Schedule.good (s : Schedule) := checked s.lo s.hi s.edIndex s.extra s.data=true
end WaringFieldSmall
