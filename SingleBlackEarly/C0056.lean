import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0056 : checkSingleBlack (4, -2) 13685 .east (6, -6) (-20, -15) = true := by
  decide +kernel

end LangtonsAnt
