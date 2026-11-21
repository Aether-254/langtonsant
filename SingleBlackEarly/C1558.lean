import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1558 : checkSingleBlackFast (-33, -8) 19503 .east (19, -5) (-24, -37) = true := by
  decide +kernel

end LangtonsAnt
