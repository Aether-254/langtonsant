import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1715 : checkSingleBlackFast (-48, -25) 13743 .west (11, 21) (-40, 1) = true := by
  decide +kernel

end LangtonsAnt
