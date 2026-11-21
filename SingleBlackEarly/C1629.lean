import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1629 : checkSingleBlackFast2 (-40, -18) 16999 .east (10, 2) (-25, -10) = true := by
  decide +kernel

end LangtonsAnt
