import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1697 : checkSingleBlackFast (-47, -23) 13743 .west (10, 21) (-40, 2) = true := by
  decide +kernel

end LangtonsAnt
