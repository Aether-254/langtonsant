import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1538 : checkSingleBlackFast (-31, -9) 26242 .south (-2, -8) (-29, -13) = true := by
  decide +kernel

end LangtonsAnt
