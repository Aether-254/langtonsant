import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0855 : checkSingleBlack (-9, 9) 18704 .south (0, -8) (-26, -26) = true := by
  decide +kernel

end LangtonsAnt
