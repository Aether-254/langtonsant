import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0813 : checkSingleBlack (26, -3) 46925 .east (-12, -18) (-40, -25) = true := by
  decide +kernel

end LangtonsAnt
