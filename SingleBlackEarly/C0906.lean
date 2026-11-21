import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0906 : checkSingleBlack (-12, 9) 13988 .north (0, 0) (-26, -12) = true := by
  decide +kernel

end LangtonsAnt
