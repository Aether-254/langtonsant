import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1603 : checkSingleBlackFast (-38, -13) 30852 .south (2, 6) (-40, -18) = true := by
  decide +kernel

end LangtonsAnt
