import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1650 : checkSingleBlack (-42, -18) 13475 .west (8, 18) (-37, -2) = true := by
  decide +kernel

end LangtonsAnt
