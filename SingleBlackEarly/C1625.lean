import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1625 : checkSingleBlackFast2 (-40, -15) 16875 .east (8, 11) (-14, -28) = true := by
  decide +kernel

end LangtonsAnt
