import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1642 : checkSingleBlackFast2 (-42, -14) 16161 .west (14, 20) (-40, -3) = true := by
  decide +kernel

end LangtonsAnt
