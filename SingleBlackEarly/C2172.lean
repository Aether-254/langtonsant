import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2172 : checkSingleBlackFast (-91, -64) 20394 .north (37, 30) (-64, -43) = true := by
  decide +kernel

end LangtonsAnt
