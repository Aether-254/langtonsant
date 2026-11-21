import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2102 : checkSingleBlack (-83, -57) 13660 .north (30, 22) (-56, -38) = true := by
  decide +kernel

end LangtonsAnt
