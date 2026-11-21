import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1534 : checkSingleBlack (-33, -6) 13418 .north (6, 0) (-33, -11) = true := by
  decide +kernel

end LangtonsAnt
