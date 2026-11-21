import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1738 : checkSingleBlack (-50, -26) 13891 .west (12, 22) (-41, 2) = true := by
  decide +kernel

end LangtonsAnt
