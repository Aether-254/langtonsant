import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1533 : checkSingleBlackFast (-32, -6) 11172 .north (5, 0) (-31, -10) = true := by
  decide +kernel

end LangtonsAnt
