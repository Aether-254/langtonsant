import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0792 : checkSingleBlackFast (25, -9) 26140 .north (-10, 8) (-40, 4) = true := by
  decide +kernel

end LangtonsAnt
