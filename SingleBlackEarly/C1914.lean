import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1914 : checkSingleBlack (-66, -42) 14723 .west (20, 30) (-49, 10) = true := by
  decide +kernel

end LangtonsAnt
