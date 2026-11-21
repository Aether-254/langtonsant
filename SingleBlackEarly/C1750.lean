import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1750 : checkSingleBlackFast2 (-51, -25) 11996 .north (14, 6) (-40, -22) = true := by
  decide +kernel

end LangtonsAnt
