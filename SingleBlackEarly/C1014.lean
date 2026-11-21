import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1014 : checkSingleBlack (-11, 6) 13736 .south (-12, 5) (-28, -7) = true := by
  decide +kernel

end LangtonsAnt
