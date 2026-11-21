import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1870 : checkSingleBlack (-62, -38) 14515 .west (18, 28) (-47, 8) = true := by
  decide +kernel

end LangtonsAnt
