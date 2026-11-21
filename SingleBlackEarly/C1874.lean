import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1874 : checkSingleBlack (-61, -40) 14858 .north (24, 12) (-51, -23) = true := by
  decide +kernel

end LangtonsAnt
