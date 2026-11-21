import PeriodicWordFast
import PeriodicNative.P18B0

namespace LangtonsAnt

theorem checkNoWords_native_18 : checkNoWords 18 = true := by
  apply checkNoWords_of_fastBlocks (width := 262144) (blocks := 1) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_18_0
  | n + 1, h => exact absurd h (by omega)

end LangtonsAnt
