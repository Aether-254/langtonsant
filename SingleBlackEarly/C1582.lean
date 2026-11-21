import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1582 : checkSingleBlackFast (-35, -13) 23593 .west (2, 8) (-40, -3) = true := by
  decide +kernel

end LangtonsAnt
