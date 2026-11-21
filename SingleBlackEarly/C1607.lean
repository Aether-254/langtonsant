import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1607 : checkSingleBlackFast (-38, -16) 26385 .west (7, 8) (-40, -8) = true := by
  decide +kernel

end LangtonsAnt
