import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0924 : checkSingleBlack (-10, 13) 14752 .north (2, 1) (-28, -1) = true := by
  decide +kernel

end LangtonsAnt
