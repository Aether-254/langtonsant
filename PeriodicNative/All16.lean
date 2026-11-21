import PeriodicWordFast
import PeriodicNative.P16B0

namespace LangtonsAnt

theorem checkNoWords_native_16 : checkNoWords 16 = true := by
  apply checkNoWords_of_fastBlocks (width := 65536) (blocks := 1) (by decide) (by decide)
  intro k hk
  match k, hk with
  | 0, _ => exact fastScan_16_0
  | n + 1, h => exact absurd h (by omega)

end LangtonsAnt
