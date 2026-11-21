import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2176 : checkSingleBlackFast2 (-89, -67) 17353 .west (32, 41) (-61, 21) = true := by
  decide +kernel

end LangtonsAnt
