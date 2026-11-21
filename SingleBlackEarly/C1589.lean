import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1589 : checkSingleBlackFast (-35, -15) 31434 .south (9, -3) (-40, -18) = true := by
  decide +kernel

end LangtonsAnt
