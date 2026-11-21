import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1397 : checkSingleBlackFast (-15, 3) 22300 .north (-4, 4) (-2, -28) = true := by
  decide +kernel

end LangtonsAnt
