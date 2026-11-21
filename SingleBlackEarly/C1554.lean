import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1554 : checkSingleBlack (-34, -6) 15745 .west (10, 16) (-36, -7) = true := by
  decide +kernel

end LangtonsAnt
