import SingleBlackCheck

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1632 : checkSingleBlack (-39, -18) 13714 .north (13, 1) (-40, -12) = true := by
  decide +kernel

end LangtonsAnt
