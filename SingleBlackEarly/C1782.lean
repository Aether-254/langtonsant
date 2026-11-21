import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1782 : checkSingleBlack (-54, -30) 14099 .west (14, 24) (-43, 4) = true := by
  decide +kernel

end LangtonsAnt
