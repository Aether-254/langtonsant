import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1293 : checkSingleBlackFast (-5, 21) 20186 .north (-6, -1) (-29, -24) = true := by
  decide +kernel

end LangtonsAnt
