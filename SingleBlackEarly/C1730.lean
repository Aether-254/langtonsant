import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1730 : checkSingleBlack (-50, -22) 16577 .west (18, 24) (-44, 1) = true := by
  decide +kernel

end LangtonsAnt
