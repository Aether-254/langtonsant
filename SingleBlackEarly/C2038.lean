import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2038 : checkSingleBlackFast2 (-78, -50) 18033 .west (32, 38) (-58, 15) = true := by
  decide +kernel

end LangtonsAnt
