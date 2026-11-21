import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1536 : checkSingleBlackFast (-31, -6) 19399 .east (18, -6) (-25, -36) = true := by
  decide +kernel

end LangtonsAnt
