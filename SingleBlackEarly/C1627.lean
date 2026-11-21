import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1627 : checkSingleBlackFast (-40, -17) 13327 .west (7, 17) (-36, -3) = true := by
  decide +kernel

end LangtonsAnt
