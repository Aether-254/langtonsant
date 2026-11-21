import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0746 : checkSingleBlackFast2 (22, -13) 10493 .west (-13, 8) (-22, -20) = true := by
  decide +kernel

end LangtonsAnt
