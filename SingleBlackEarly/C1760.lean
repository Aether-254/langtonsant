import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1760 : checkSingleBlack (-52, -28) 13995 .west (13, 23) (-42, 3) = true := by
  decide +kernel

end LangtonsAnt
