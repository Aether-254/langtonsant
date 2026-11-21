import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1638 : checkSingleBlack (-38, -18) 14884 .north (14, 4) (-40, -20) = true := by
  decide +kernel

end LangtonsAnt
