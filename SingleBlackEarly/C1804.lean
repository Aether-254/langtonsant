import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1804 : checkSingleBlack (-56, -32) 14203 .west (15, 25) (-44, 5) = true := by
  decide +kernel

end LangtonsAnt
