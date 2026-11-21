import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1771 : checkSingleBlackFast (-49, -31) 12008 .north (14, 6) (-40, -22) = true := by
  decide +kernel

end LangtonsAnt
