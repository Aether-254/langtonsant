import PeriodicWordFast
import PeriodicNative.All36G0
import PeriodicNative.All36G1
import PeriodicNative.All36G2
import PeriodicNative.All36G3
import PeriodicNative.All36G4
import PeriodicNative.All36G5
import PeriodicNative.All36G6
import PeriodicNative.All36G7
import PeriodicNative.All36G8
import PeriodicNative.All36G9
import PeriodicNative.All36G10
import PeriodicNative.All36G11
import PeriodicNative.All36G12
import PeriodicNative.All36G13
import PeriodicNative.All36G14
import PeriodicNative.All36G15

namespace LangtonsAnt

theorem checkNoWords_native_36 : checkNoWords 36 = true := by
  apply checkNoWords_of_fastBlocks (width := 16777216) (blocks := 4096) (by decide) (by decide)
  intro k hk
  have hq : k / 256 < 16 := by omega
  have hr : k % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [show k = 256 * (k / 256) + k % 256 by omega]
  generalize k / 256 = q at hq ⊢
  generalize k % 256 = r at hr ⊢
  match q, hq with
  | 0, _ => exact fastScan_36_group_0 r hr
  | 1, _ => exact fastScan_36_group_1 r hr
  | 2, _ => exact fastScan_36_group_2 r hr
  | 3, _ => exact fastScan_36_group_3 r hr
  | 4, _ => exact fastScan_36_group_4 r hr
  | 5, _ => exact fastScan_36_group_5 r hr
  | 6, _ => exact fastScan_36_group_6 r hr
  | 7, _ => exact fastScan_36_group_7 r hr
  | 8, _ => exact fastScan_36_group_8 r hr
  | 9, _ => exact fastScan_36_group_9 r hr
  | 10, _ => exact fastScan_36_group_10 r hr
  | 11, _ => exact fastScan_36_group_11 r hr
  | 12, _ => exact fastScan_36_group_12 r hr
  | 13, _ => exact fastScan_36_group_13 r hr
  | 14, _ => exact fastScan_36_group_14 r hr
  | 15, _ => exact fastScan_36_group_15 r hr
  | n + 16, h => exact absurd h (by omega)

end LangtonsAnt
