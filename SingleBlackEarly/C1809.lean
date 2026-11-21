import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1809 : checkSingleBlack (-55, -35) 45162 .north (39, 22) (-66, -5) = true := by
  decide +kernel

end LangtonsAnt
