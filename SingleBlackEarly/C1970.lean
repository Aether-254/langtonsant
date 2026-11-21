import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1970 : checkSingleBlack (-71, -45) 13036 .north (24, 16) (-50, -32) = true := by
  decide +kernel

end LangtonsAnt
