import PeriodicWordFast
import PeriodicNative.P30B0
import PeriodicNative.P30B1
import PeriodicNative.P30B2
import PeriodicNative.P30B3
import PeriodicNative.P30B4
import PeriodicNative.P30B5
import PeriodicNative.P30B6
import PeriodicNative.P30B7
import PeriodicNative.P30B8
import PeriodicNative.P30B9
import PeriodicNative.P30B10
import PeriodicNative.P30B11
import PeriodicNative.P30B12
import PeriodicNative.P30B13
import PeriodicNative.P30B14
import PeriodicNative.P30B15
import PeriodicNative.P30B16
import PeriodicNative.P30B17
import PeriodicNative.P30B18
import PeriodicNative.P30B19
import PeriodicNative.P30B20
import PeriodicNative.P30B21
import PeriodicNative.P30B22
import PeriodicNative.P30B23
import PeriodicNative.P30B24
import PeriodicNative.P30B25
import PeriodicNative.P30B26
import PeriodicNative.P30B27
import PeriodicNative.P30B28
import PeriodicNative.P30B29
import PeriodicNative.P30B30
import PeriodicNative.P30B31
import PeriodicNative.P30B32
import PeriodicNative.P30B33
import PeriodicNative.P30B34
import PeriodicNative.P30B35
import PeriodicNative.P30B36
import PeriodicNative.P30B37
import PeriodicNative.P30B38
import PeriodicNative.P30B39
import PeriodicNative.P30B40
import PeriodicNative.P30B41
import PeriodicNative.P30B42
import PeriodicNative.P30B43
import PeriodicNative.P30B44
import PeriodicNative.P30B45
import PeriodicNative.P30B46
import PeriodicNative.P30B47
import PeriodicNative.P30B48
import PeriodicNative.P30B49
import PeriodicNative.P30B50
import PeriodicNative.P30B51
import PeriodicNative.P30B52
import PeriodicNative.P30B53
import PeriodicNative.P30B54
import PeriodicNative.P30B55
import PeriodicNative.P30B56
import PeriodicNative.P30B57
import PeriodicNative.P30B58
import PeriodicNative.P30B59
import PeriodicNative.P30B60
import PeriodicNative.P30B61
import PeriodicNative.P30B62
import PeriodicNative.P30B63

namespace LangtonsAnt

theorem checkNoWords_native_30 : checkNoWords 30 = true := by
  apply checkNoWords_of_fastBlocks (width := 16777216) (blocks := 64) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_30_0
  | 1, _ => exact fastScan_30_1
  | 2, _ => exact fastScan_30_2
  | 3, _ => exact fastScan_30_3
  | 4, _ => exact fastScan_30_4
  | 5, _ => exact fastScan_30_5
  | 6, _ => exact fastScan_30_6
  | 7, _ => exact fastScan_30_7
  | 8, _ => exact fastScan_30_8
  | 9, _ => exact fastScan_30_9
  | 10, _ => exact fastScan_30_10
  | 11, _ => exact fastScan_30_11
  | 12, _ => exact fastScan_30_12
  | 13, _ => exact fastScan_30_13
  | 14, _ => exact fastScan_30_14
  | 15, _ => exact fastScan_30_15
  | 16, _ => exact fastScan_30_16
  | 17, _ => exact fastScan_30_17
  | 18, _ => exact fastScan_30_18
  | 19, _ => exact fastScan_30_19
  | 20, _ => exact fastScan_30_20
  | 21, _ => exact fastScan_30_21
  | 22, _ => exact fastScan_30_22
  | 23, _ => exact fastScan_30_23
  | 24, _ => exact fastScan_30_24
  | 25, _ => exact fastScan_30_25
  | 26, _ => exact fastScan_30_26
  | 27, _ => exact fastScan_30_27
  | 28, _ => exact fastScan_30_28
  | 29, _ => exact fastScan_30_29
  | 30, _ => exact fastScan_30_30
  | 31, _ => exact fastScan_30_31
  | 32, _ => exact fastScan_30_32
  | 33, _ => exact fastScan_30_33
  | 34, _ => exact fastScan_30_34
  | 35, _ => exact fastScan_30_35
  | 36, _ => exact fastScan_30_36
  | 37, _ => exact fastScan_30_37
  | 38, _ => exact fastScan_30_38
  | 39, _ => exact fastScan_30_39
  | 40, _ => exact fastScan_30_40
  | 41, _ => exact fastScan_30_41
  | 42, _ => exact fastScan_30_42
  | 43, _ => exact fastScan_30_43
  | 44, _ => exact fastScan_30_44
  | 45, _ => exact fastScan_30_45
  | 46, _ => exact fastScan_30_46
  | 47, _ => exact fastScan_30_47
  | 48, _ => exact fastScan_30_48
  | 49, _ => exact fastScan_30_49
  | 50, _ => exact fastScan_30_50
  | 51, _ => exact fastScan_30_51
  | 52, _ => exact fastScan_30_52
  | 53, _ => exact fastScan_30_53
  | 54, _ => exact fastScan_30_54
  | 55, _ => exact fastScan_30_55
  | 56, _ => exact fastScan_30_56
  | 57, _ => exact fastScan_30_57
  | 58, _ => exact fastScan_30_58
  | 59, _ => exact fastScan_30_59
  | 60, _ => exact fastScan_30_60
  | 61, _ => exact fastScan_30_61
  | 62, _ => exact fastScan_30_62
  | 63, _ => exact fastScan_30_63
  | n + 64, h => exact absurd h (by omega)

end LangtonsAnt
