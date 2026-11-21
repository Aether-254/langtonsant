import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1514 : checkSingleBlackFast (-29, -4) 19295 .east (17, -7) (-26, -35) = true := by
  decide +kernel

end LangtonsAnt
