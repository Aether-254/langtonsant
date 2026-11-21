import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1915 : checkSingleBlackFast (-66, -44) 19235 .east (23, 17) (-10, -35) = true := by
  decide +kernel

end LangtonsAnt
