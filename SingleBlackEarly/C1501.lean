import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1501 : checkSingleBlack (-27, -7) 49124 .south (3, -7) (-39, -3) = true := by
  decide +kernel

end LangtonsAnt
