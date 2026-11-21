import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1562 : checkSingleBlack (-34, -10) 13059 .west (4, 14) (-33, -6) = true := by
  decide +kernel

end LangtonsAnt
