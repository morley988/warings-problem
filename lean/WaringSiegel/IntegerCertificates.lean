import Std

/-!
# Independent integer certificates for the two threshold branches

No external rational arithmetic is trusted by these proofs. For every index
the denominator is checked positive, every candidate is at least s-1, and
one candidate is strictly below s. Consequently s is exactly floor(min B)+1.
This certifies the numerical threshold only, not the analytic inequalities.
All closed computations use kernel-reduced `decide`, never `native_decide`.
-/

namespace WaringSiegel.IntegerCertificates

def denominator (k r : Nat) : Int := (k : Int) - (r : Int) + 1

def firstNumerator (k r : Nat) : Int :=
  (k : Int)^2 * denominator k r - (r : Int) * ((k : Int) - r - 1)

def secondNumerator (k j : Nat) : Int :=
  (k : Int)^2 * denominator k j - ((k : Int) * j - (2 : Int)^j)

def ThresholdCertificate (k s : Nat) : Prop :=
  (∀ r : Fin k, 0 < denominator k (r.val+1) ∧
    ((s : Int)-1)*denominator k (r.val+1) ≤ firstNumerator k (r.val+1)) ∧
  (∀ j : Fin k, 0 < denominator k (j.val+1) ∧
    ((s : Int)-1)*denominator k (j.val+1) ≤ secondNumerator k (j.val+1)) ∧
  ((∃ r : Fin k, firstNumerator k (r.val+1) < (s : Int)*denominator k (r.val+1)) ∨
   (∃ j : Fin k, secondNumerator k (j.val+1) < (s : Int)*denominator k (j.val+1)))

instance (k s : Nat) : Decidable (ThresholdCertificate k s) := by
  unfold ThresholdCertificate
  infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem threshold_3 : ThresholdCertificate 3 9 := by decide
theorem threshold_4 : ThresholdCertificate 4 15 := by decide
theorem threshold_5 : ThresholdCertificate 5 23 := by decide
theorem threshold_6 : ThresholdCertificate 6 34 := by decide
theorem threshold_7 : ThresholdCertificate 7 47 := by decide
theorem threshold_8 : ThresholdCertificate 8 61 := by decide
theorem threshold_9 : ThresholdCertificate 9 78 := by decide
theorem threshold_10 : ThresholdCertificate 10 97 := by decide
theorem threshold_11 : ThresholdCertificate 11 117 := by decide
theorem threshold_12 : ThresholdCertificate 12 140 := by decide
theorem threshold_13 : ThresholdCertificate 13 164 := by decide
theorem threshold_14 : ThresholdCertificate 14 191 := by decide
theorem threshold_15 : ThresholdCertificate 15 219 := by decide
theorem threshold_16 : ThresholdCertificate 16 249 := by decide
theorem threshold_17 : ThresholdCertificate 17 282 := by decide
theorem threshold_18 : ThresholdCertificate 18 316 := by decide
theorem threshold_19 : ThresholdCertificate 19 352 := by decide
theorem threshold_20 : ThresholdCertificate 20 391 := by decide
theorem threshold_21 : ThresholdCertificate 21 431 := by decide
theorem threshold_22 : ThresholdCertificate 22 473 := by decide
theorem threshold_23 : ThresholdCertificate 23 517 := by decide
theorem threshold_24 : ThresholdCertificate 24 564 := by decide
theorem threshold_25 : ThresholdCertificate 25 612 := by decide
theorem threshold_26 : ThresholdCertificate 26 662 := by decide
theorem threshold_27 : ThresholdCertificate 27 715 := by decide
theorem threshold_28 : ThresholdCertificate 28 769 := by decide
theorem threshold_29 : ThresholdCertificate 29 825 := by decide
theorem threshold_30 : ThresholdCertificate 30 883 := by decide
theorem threshold_31 : ThresholdCertificate 31 944 := by decide
theorem threshold_32 : ThresholdCertificate 32 1006 := by decide
theorem threshold_33 : ThresholdCertificate 33 1070 := by decide
theorem threshold_34 : ThresholdCertificate 34 1136 := by decide
theorem threshold_35 : ThresholdCertificate 35 1205 := by decide
theorem threshold_36 : ThresholdCertificate 36 1275 := by decide
theorem threshold_37 : ThresholdCertificate 37 1347 := by decide
theorem threshold_38 : ThresholdCertificate 38 1421 := by decide
theorem threshold_39 : ThresholdCertificate 39 1497 := by decide
theorem threshold_40 : ThresholdCertificate 40 1576 := by decide
theorem threshold_41 : ThresholdCertificate 41 1656 := by decide
theorem threshold_42 : ThresholdCertificate 42 1738 := by decide
theorem threshold_43 : ThresholdCertificate 43 1822 := by decide
theorem threshold_44 : ThresholdCertificate 44 1909 := by decide
theorem threshold_45 : ThresholdCertificate 45 1997 := by decide
theorem threshold_46 : ThresholdCertificate 46 2087 := by decide
theorem threshold_47 : ThresholdCertificate 47 2179 := by decide
theorem threshold_48 : ThresholdCertificate 48 2273 := by decide
theorem threshold_49 : ThresholdCertificate 49 2370 := by decide
theorem threshold_50 : ThresholdCertificate 50 2468 := by decide
theorem threshold_51 : ThresholdCertificate 51 2568 := by decide
theorem threshold_52 : ThresholdCertificate 52 2670 := by decide
theorem threshold_53 : ThresholdCertificate 53 2774 := by decide
theorem threshold_54 : ThresholdCertificate 54 2881 := by decide
theorem threshold_55 : ThresholdCertificate 55 2989 := by decide
theorem threshold_56 : ThresholdCertificate 56 3099 := by decide
theorem threshold_57 : ThresholdCertificate 57 3211 := by decide
theorem threshold_58 : ThresholdCertificate 58 3325 := by decide
theorem threshold_59 : ThresholdCertificate 59 3441 := by decide
theorem threshold_60 : ThresholdCertificate 60 3560 := by decide
theorem threshold_61 : ThresholdCertificate 61 3680 := by decide
theorem threshold_62 : ThresholdCertificate 62 3802 := by decide
theorem threshold_63 : ThresholdCertificate 63 3926 := by decide
theorem threshold_64 : ThresholdCertificate 64 4052 := by decide
theorem threshold_65 : ThresholdCertificate 65 4181 := by decide
theorem threshold_66 : ThresholdCertificate 66 4311 := by decide
theorem threshold_67 : ThresholdCertificate 67 4443 := by decide
theorem threshold_68 : ThresholdCertificate 68 4577 := by decide
theorem threshold_69 : ThresholdCertificate 69 4713 := by decide
theorem threshold_70 : ThresholdCertificate 70 4851 := by decide
theorem threshold_71 : ThresholdCertificate 71 4992 := by decide
theorem threshold_72 : ThresholdCertificate 72 5134 := by decide
theorem threshold_73 : ThresholdCertificate 73 5278 := by decide
theorem threshold_74 : ThresholdCertificate 74 5424 := by decide
theorem threshold_75 : ThresholdCertificate 75 5572 := by decide
theorem threshold_76 : ThresholdCertificate 76 5722 := by decide
theorem threshold_77 : ThresholdCertificate 77 5875 := by decide
theorem threshold_78 : ThresholdCertificate 78 6029 := by decide
theorem threshold_79 : ThresholdCertificate 79 6185 := by decide
theorem threshold_80 : ThresholdCertificate 80 6343 := by decide
theorem threshold_81 : ThresholdCertificate 81 6503 := by decide
theorem threshold_82 : ThresholdCertificate 82 6665 := by decide
theorem threshold_83 : ThresholdCertificate 83 6829 := by decide
theorem threshold_84 : ThresholdCertificate 84 6996 := by decide
theorem threshold_85 : ThresholdCertificate 85 7164 := by decide
theorem threshold_86 : ThresholdCertificate 86 7334 := by decide
theorem threshold_87 : ThresholdCertificate 87 7506 := by decide
theorem threshold_88 : ThresholdCertificate 88 7680 := by decide
theorem threshold_89 : ThresholdCertificate 89 7856 := by decide
theorem threshold_90 : ThresholdCertificate 90 8035 := by decide
theorem threshold_91 : ThresholdCertificate 91 8215 := by decide
theorem threshold_92 : ThresholdCertificate 92 8397 := by decide
theorem threshold_93 : ThresholdCertificate 93 8581 := by decide
theorem threshold_94 : ThresholdCertificate 94 8767 := by decide
theorem threshold_95 : ThresholdCertificate 95 8955 := by decide
theorem threshold_96 : ThresholdCertificate 96 9145 := by decide
theorem threshold_97 : ThresholdCertificate 97 9338 := by decide
theorem threshold_98 : ThresholdCertificate 98 9532 := by decide
theorem threshold_99 : ThresholdCertificate 99 9728 := by decide
theorem threshold_100 : ThresholdCertificate 100 9926 := by decide

end WaringSiegel.IntegerCertificates
