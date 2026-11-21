import PeriodicWordFast
import PeriodicNative.P20B0

namespace LangtonsAnt

theorem checkNoWords_native_20 : checkNoWords 20 = true := by
  apply checkNoWords_of_fastBlocks (width := 1048576) (blocks := 1) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_20_0
  | n + 1, h => exact absurd h (by omega)

end LangtonsAnt
