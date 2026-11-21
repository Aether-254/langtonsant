import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1826 : checkSingleBlack (-58, -34) 14307 .west (16, 26) (-45, 6) = true := by
  decide +kernel

end LangtonsAnt
