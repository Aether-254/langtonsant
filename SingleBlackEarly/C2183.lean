import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2183 : checkSingleBlack (-89, -69) 46930 .north (56, 39) (-83, -22) = true := by
  decide +kernel

end LangtonsAnt
