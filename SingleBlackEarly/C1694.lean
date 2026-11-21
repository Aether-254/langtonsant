import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1694 : checkSingleBlack (-46, -22) 13683 .west (10, 20) (-39, 0) = true := by
  decide +kernel

end LangtonsAnt
