import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0548 : checkSingleBlackFast2 (10, -6) 18411 .west (-2, 6) (-27, -22) = true := by
  decide +kernel

end LangtonsAnt
