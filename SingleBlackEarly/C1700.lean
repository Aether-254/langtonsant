import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1700 : checkSingleBlack (-46, -25) 40569 .east (13, -2) (-38, -12) = true := by
  decide +kernel

end LangtonsAnt
