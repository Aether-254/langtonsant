import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1634 : checkSingleBlackFast (-40, -19) 21503 .east (10, -6) (-15, -26) = true := by
  decide +kernel

end LangtonsAnt
