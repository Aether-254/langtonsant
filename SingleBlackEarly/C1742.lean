import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1742 : checkSingleBlack (-49, -28) 14234 .north (18, 6) (-45, -17) = true := by
  decide +kernel

end LangtonsAnt
