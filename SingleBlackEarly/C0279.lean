import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0279 : checkSingleBlackFast (14, 9) 3807 .east (-5, 0) (-13, -13) = true := by
  decide +kernel

end LangtonsAnt
