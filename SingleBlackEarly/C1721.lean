import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1721 : checkSingleBlack (-47, -27) 44746 .north (35, 18) (-62, -1) = true := by
  decide +kernel

end LangtonsAnt
