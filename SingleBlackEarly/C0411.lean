import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0411 : checkSingleBlackFast2 (16, -4) 16127 .west (1, -2) (-25, -15) = true := by
  decide +kernel

end LangtonsAnt
