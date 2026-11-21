import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2117 : checkSingleBlack (-83, -63) 46618 .north (53, 36) (-80, -19) = true := by
  decide +kernel

end LangtonsAnt
