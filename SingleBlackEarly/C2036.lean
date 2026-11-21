import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2036 : checkSingleBlack (-77, -51) 13348 .north (27, 19) (-53, -35) = true := by
  decide +kernel

end LangtonsAnt
