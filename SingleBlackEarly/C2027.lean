import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2027 : checkSingleBlackFast2 (-77, -53) 15303 .west (25, 36) (-55, 17) = true := by
  decide +kernel

end LangtonsAnt
