import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1628 : checkSingleBlack (-40, -16) 13371 .west (7, 17) (-36, -3) = true := by
  decide +kernel

end LangtonsAnt
