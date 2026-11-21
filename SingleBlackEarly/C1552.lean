import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1552 : checkSingleBlackFast2 (-33, -7) 11060 .north (5, 0) (-31, -10) = true := by
  decide +kernel

end LangtonsAnt
