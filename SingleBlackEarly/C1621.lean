import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1621 : checkSingleBlackFast (-40, -14) 11588 .north (9, 1) (-35, -17) = true := by
  decide +kernel

end LangtonsAnt
