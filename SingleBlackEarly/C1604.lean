import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1604 : checkSingleBlack (-37, -15) 14649 .west (6, 15) (-35, -5) = true := by
  decide +kernel

end LangtonsAnt
