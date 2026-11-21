import PeriodicWordFast
import PeriodicNative.P22B0

namespace LangtonsAnt

theorem checkNoWords_native_22 : checkNoWords 22 = true := by
  apply checkNoWords_of_fastBlocks (width := 4194304) (blocks := 1) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_22_0
  | n + 1, h => exact absurd h (by omega)

end LangtonsAnt
