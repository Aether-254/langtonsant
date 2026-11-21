import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1362 : checkSingleBlackFast (-14, 6) 21584 .north (-5, 1) (-5, -33) = true := by
  decide +kernel

end LangtonsAnt
