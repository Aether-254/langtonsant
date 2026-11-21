import PeriodicWordFast
import PeriodicNative.P28B0
import PeriodicNative.P28B1
import PeriodicNative.P28B2
import PeriodicNative.P28B3
import PeriodicNative.P28B4
import PeriodicNative.P28B5
import PeriodicNative.P28B6
import PeriodicNative.P28B7
import PeriodicNative.P28B8
import PeriodicNative.P28B9
import PeriodicNative.P28B10
import PeriodicNative.P28B11
import PeriodicNative.P28B12
import PeriodicNative.P28B13
import PeriodicNative.P28B14
import PeriodicNative.P28B15

namespace LangtonsAnt

theorem checkNoWords_native_28 : checkNoWords 28 = true := by
  apply checkNoWords_of_fastBlocks (width := 16777216) (blocks := 16) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_28_0
  | 1, _ => exact fastScan_28_1
  | 2, _ => exact fastScan_28_2
  | 3, _ => exact fastScan_28_3
  | 4, _ => exact fastScan_28_4
  | 5, _ => exact fastScan_28_5
  | 6, _ => exact fastScan_28_6
  | 7, _ => exact fastScan_28_7
  | 8, _ => exact fastScan_28_8
  | 9, _ => exact fastScan_28_9
  | 10, _ => exact fastScan_28_10
  | 11, _ => exact fastScan_28_11
  | 12, _ => exact fastScan_28_12
  | 13, _ => exact fastScan_28_13
  | 14, _ => exact fastScan_28_14
  | 15, _ => exact fastScan_28_15
  | n + 16, h => exact absurd h (by omega)

end LangtonsAnt
