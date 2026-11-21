import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1831 : checkSingleBlack (-57, -37) 45266 .north (40, 23) (-67, -6) = true := by
  decide +kernel

end LangtonsAnt
