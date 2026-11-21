import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0372 : checkSingleBlackFast (14, -3) 32895 .east (-3, -1) (-14, -29) = true := by
  decide +kernel

end LangtonsAnt
