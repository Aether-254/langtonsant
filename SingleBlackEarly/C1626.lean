import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1626 : checkSingleBlack (-39, -17) 14753 .west (7, 16) (-36, -4) = true := by
  decide +kernel

end LangtonsAnt
