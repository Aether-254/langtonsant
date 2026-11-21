import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1716 : checkSingleBlack (-48, -24) 13787 .west (11, 21) (-40, 1) = true := by
  decide +kernel

end LangtonsAnt
