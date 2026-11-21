import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1434 : checkSingleBlackFast (-21, 0) 23500 .north (-5, 2) (-5, -32) = true := by
  decide +kernel

end LangtonsAnt
