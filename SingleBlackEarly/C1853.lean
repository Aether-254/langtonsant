import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1853 : checkSingleBlack (-59, -39) 45370 .north (41, 24) (-68, -7) = true := by
  decide +kernel

end LangtonsAnt
