import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2022 : checkSingleBlackFast2 (-75, -53) 16625 .west (25, 34) (-54, 14) = true := by
  decide +kernel

end LangtonsAnt
