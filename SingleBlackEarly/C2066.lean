import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2066 : checkSingleBlackFast2 (-79, -57) 16833 .west (27, 36) (-56, 16) = true := by
  decide +kernel

end LangtonsAnt
