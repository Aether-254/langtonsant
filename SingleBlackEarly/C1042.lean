import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1042 : checkSingleBlackFast2 (-11, -3) 17255 .west (-1, 8) (-29, -7) = true := by
  decide +kernel

end LangtonsAnt
