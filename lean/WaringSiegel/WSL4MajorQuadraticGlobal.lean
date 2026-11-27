import WaringSiegel.WSL4MajorQuadraticTarget
import WaringSiegel.WSL4LocalSquaresTarget

/-! # Unconditional uniform quadratic Waring–Siegel bound at 256 variables -/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4

theorem quadratic_waringSiegelBound (K : Type*) [Field K] [NumberField K] :
    WaringSiegelBound K 2 256 := by
  apply bound_of_localConditionalBound (quadratic_localConditionalBound K)
  intro ν hν
  exact WSL4Local.eligible_squares_local_solvable (by norm_num) hν

theorem quadratic_uniformWaringSiegelBound : UniformWaringSiegelBound 2 256 := by
  intro K _ _
  exact quadratic_waringSiegelBound K

#print axioms quadratic_waringSiegelBound
#print axioms quadratic_uniformWaringSiegelBound
end WaringSiegel.WSL4
