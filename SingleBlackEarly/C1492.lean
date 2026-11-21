import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1492 : checkSingleBlackFast (-27, -2) 29052 .north (6, -10) (-40, -14) = true := by
  decide +kernel

end LangtonsAnt
