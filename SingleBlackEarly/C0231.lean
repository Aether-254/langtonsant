import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0231 : checkSingleBlackFast (7, 10) 2201 .east (-2, -9) (-13, -3) = true := by
  decide +kernel

end LangtonsAnt
