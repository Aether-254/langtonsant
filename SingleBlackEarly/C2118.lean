import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2118 : checkSingleBlackFast (-84, -63) 20861 .east (33, 23) (17, -56) = true := by
  decide +kernel

end LangtonsAnt
