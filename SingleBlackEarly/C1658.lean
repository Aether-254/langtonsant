import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1658 : checkSingleBlackFast (-40, -22) 27523 .east (23, 11) (-18, -33) = true := by
  decide +kernel

end LangtonsAnt
