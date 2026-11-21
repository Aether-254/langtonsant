import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1620 : checkSingleBlackFast2 (-40, -12) 16057 .west (13, 19) (-39, -4) = true := by
  decide +kernel

end LangtonsAnt
