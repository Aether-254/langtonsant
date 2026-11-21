import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1585 : checkSingleBlackFast (-36, -14) 22301 .east (10, -10) (-34, -5) = true := by
  decide +kernel

end LangtonsAnt
