import PeriodicWordFast
import PeriodicNative.P26B0
import PeriodicNative.P26B1
import PeriodicNative.P26B2
import PeriodicNative.P26B3
import PeriodicNative.P26B4
import PeriodicNative.P26B5
import PeriodicNative.P26B6
import PeriodicNative.P26B7
import PeriodicNative.P26B8
import PeriodicNative.P26B9
import PeriodicNative.P26B10
import PeriodicNative.P26B11
import PeriodicNative.P26B12
import PeriodicNative.P26B13
import PeriodicNative.P26B14
import PeriodicNative.P26B15

namespace LangtonsAnt

theorem checkNoWords_native_26 : checkNoWords 26 = true := by
  apply checkNoWords_of_fastBlocks (width := 4194304) (blocks := 16) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_26_0
  | 1, _ => exact fastScan_26_1
  | 2, _ => exact fastScan_26_2
  | 3, _ => exact fastScan_26_3
  | 4, _ => exact fastScan_26_4
  | 5, _ => exact fastScan_26_5
  | 6, _ => exact fastScan_26_6
  | 7, _ => exact fastScan_26_7
  | 8, _ => exact fastScan_26_8
  | 9, _ => exact fastScan_26_9
  | 10, _ => exact fastScan_26_10
  | 11, _ => exact fastScan_26_11
  | 12, _ => exact fastScan_26_12
  | 13, _ => exact fastScan_26_13
  | 14, _ => exact fastScan_26_14
  | 15, _ => exact fastScan_26_15
  | n + 16, h => exact absurd h (by omega)

end LangtonsAnt
