import PeriodicWordFast
import PeriodicNative.P14B0

namespace LangtonsAnt

theorem checkNoWords_native_14 : checkNoWords 14 = true := by
  apply checkNoWords_of_fastBlocks (width := 16384) (blocks := 1) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_14_0
  | n + 1, h => exact absurd h (by omega)

end LangtonsAnt
