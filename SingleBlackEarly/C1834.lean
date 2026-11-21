import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1834 : checkSingleBlackFast (-56, -38) 28355 .east (31, 19) (-10, -41) = true := by
  decide +kernel

end LangtonsAnt
