import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1499 : checkSingleBlackFast (-29, -5) 12807 .west (1, 12) (-31, -7) = true := by
  decide +kernel

end LangtonsAnt
