import Waring.SeedCompletionTerminalIdentityRecognition
import Waring.SeedCompletionTerminalSecond

/-! # The proved polynomial recognition needed by the source diagonal count -/

noncomputable section
namespace Waring.SeedCompletionTerminalIdentity
open SeedCompletionTerminalSecond

/-- Every required weighted sparse equation follows from equality of the
literal integer source polynomials. Only the available number of coefficients
and the explicitly checked eight nonzero cumulants enter the range. -/
theorem sparse_recognition (k j J : ℕ) (hJ : J≤8) (hkj : j+2*J≤k) :
    SparseRecognition k j J := by
  intro h m n hh hm hn he r
  have hr := r.isLt
  exact natural_power_sums_of_polynomial_eq k h m n hh hm hn he
    (by omega) (by omega) (by omega)

theorem sparse_recognition_max {k j : ℕ} (hk : k≤18) (hj : 1≤j) (hjk : j≤k) :
    SparseRecognition k j ((k-j)/2) :=
  sparse_recognition k j ((k-j)/2) (by omega) (by omega)

#print axioms sparse_recognition
#print axioms sparse_recognition_max
end Waring.SeedCompletionTerminalIdentity
