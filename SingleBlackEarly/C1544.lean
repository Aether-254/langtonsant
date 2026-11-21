import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1544 : checkSingleBlackFast (-31, -10) 22370 .north (6, -6) (-39, -11) = true := by
  decide +kernel

end LangtonsAnt
