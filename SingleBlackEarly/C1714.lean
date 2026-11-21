import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1714 : checkSingleBlackFast2 (-47, -25) 15169 .west (11, 20) (-40, 0) = true := by
  decide +kernel

end LangtonsAnt
