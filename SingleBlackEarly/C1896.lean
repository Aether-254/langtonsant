import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1896 : checkSingleBlack (-63, -42) 14962 .north (25, 13) (-52, -24) = true := by
  decide +kernel

end LangtonsAnt
