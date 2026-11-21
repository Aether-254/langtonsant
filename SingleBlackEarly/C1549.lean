import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1549 : checkSingleBlackFast (-31, -12) 24337 .east (4, 1) (-13, -33) = true := by
  decide +kernel

end LangtonsAnt
