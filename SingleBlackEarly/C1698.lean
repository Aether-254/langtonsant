import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1698 : checkSingleBlack (-45, -24) 14026 .north (16, 4) (-43, -15) = true := by
  decide +kernel

end LangtonsAnt
