import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1660 : checkSingleBlack (-40, -20) 14988 .north (15, 5) (-41, -21) = true := by
  decide +kernel

end LangtonsAnt
