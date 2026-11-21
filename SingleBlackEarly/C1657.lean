import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1657 : checkSingleBlackFast (-40, -21) 19880 .north (22, 18) (-48, -10) = true := by
  decide +kernel

end LangtonsAnt
