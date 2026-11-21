import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1584 : checkSingleBlack (-36, -12) 13163 .west (5, 15) (-34, -5) = true := by
  decide +kernel

end LangtonsAnt
