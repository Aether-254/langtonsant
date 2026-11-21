import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1985 : checkSingleBlack (-71, -51) 45994 .north (47, 30) (-74, -13) = true := by
  decide +kernel

end LangtonsAnt
