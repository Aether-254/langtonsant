import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1478 : checkSingleBlackFast (-25, -4) 22720 .north (-3, 4) (-5, -32) = true := by
  decide +kernel

end LangtonsAnt
