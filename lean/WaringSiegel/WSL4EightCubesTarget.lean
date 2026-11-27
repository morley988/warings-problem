import WaringSiegel.WSL4EightCubesCompact
import WaringSiegel.MainTargets

/-! # The unchanged uniform eight-cube target for every number field -/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4
open WSL2 WSL4Local

theorem eight_cubes_number_field (K : Type*) [Field K] [NumberField K] :
    WaringSiegelBound K 3 8 := by
  obtain ⟨B,hB,_,hreduce⟩ := exists_compact_waring_reduction K 3 (by norm_num)
  exact (hreduce 8).mp (compact_eight_cubes_bound B (lt_of_lt_of_le zero_lt_one hB))

theorem eightCubesClaim_verified : EightCubesClaim := by
  intro K _ _
  exact eight_cubes_number_field K

#print axioms eightCubesClaim_verified
end WaringSiegel.WSL4
