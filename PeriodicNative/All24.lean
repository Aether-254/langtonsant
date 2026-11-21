import PeriodicWordFast
import PeriodicNative.P24B0
import PeriodicNative.P24B1
import PeriodicNative.P24B2
import PeriodicNative.P24B3

namespace LangtonsAnt

theorem checkNoWords_native_24 : checkNoWords 24 = true := by
  apply checkNoWords_of_fastBlocks (width := 4194304) (blocks := 4) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_24_0
  | 1, _ => exact fastScan_24_1
  | 2, _ => exact fastScan_24_2
  | 3, _ => exact fastScan_24_3
  | n + 4, h => exact absurd h (by omega)

end LangtonsAnt
