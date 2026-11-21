import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0624 : checkSingleBlackFast2 (7, -9) 12361 .west (-10, -1) (-19, -17) = true := by
  decide +kernel

end LangtonsAnt
