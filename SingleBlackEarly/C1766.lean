import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1766 : checkSingleBlackFast (-52, -31) 19197 .east (17, 7) (1, -40) = true := by
  decide +kernel

end LangtonsAnt
