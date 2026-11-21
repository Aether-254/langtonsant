import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1731 : checkSingleBlackFast (-50, -24) 12108 .north (14, 6) (-40, -22) = true := by
  decide +kernel

end LangtonsAnt
