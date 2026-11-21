import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1513 : checkSingleBlackFast (-31, -3) 25022 .north (10, -3) (-43, -24) = true := by
  decide +kernel

end LangtonsAnt
