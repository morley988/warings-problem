import WaringLimit.Words

/-! Arithmetic exponent-pair words with radical loss preserved at B. -/
namespace WaringSharpTail
open WaringDualEnvelope
open WaringLimit (words Entry decode)

def sharpStep (p : Pair) (move : Bool) : Pair :=
  if move then
    normalized (2*p.y-p.denominator) (2*p.x+p.denominator) (2*p.denominator)
      p.loss p.lossDen
  else
    normalized p.x (p.x+p.y+p.denominator) (2*p.denominator+2*p.x)
      (p.loss+p.lossDen) (2*p.lossDen)

def sharpPair (w : List Bool) : Pair := w.foldl sharpStep basePair

def sharpEntryOK (e : Entry) : Bool :=
  let w := decode 14 e.bits
  let p := sharpPair w
  0 < e.x && 0 < e.den && 0 < p.denominator && 0 < p.lossDen &&
    p.x*e.den == e.x*p.denominator && p.y*e.den == e.y*p.denominator &&
    p.loss ≤ p.lossDen && validWord w

theorem sharp_words_checked : words.all sharpEntryOK = true := by
  decide +kernel

#print axioms sharp_words_checked
end WaringSharpTail
