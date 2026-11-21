import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0232 : checkSingleBlackFast2 (6, 8) 16624 .south (5, -20) (1, -32) = true := by
  decide +kernel

end LangtonsAnt
