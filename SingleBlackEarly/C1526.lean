import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1526 : checkSingleBlack (-28, -10) 41479 .east (7, -3) (-14, -39) = true := by
  decide +kernel

end LangtonsAnt
