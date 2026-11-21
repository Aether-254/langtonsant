import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1743 : checkSingleBlack (-49, -29) 44850 .north (36, 19) (-63, -2) = true := by
  decide +kernel

end LangtonsAnt
