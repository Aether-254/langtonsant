import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1353 : checkSingleBlackFast (-16, 6) 24510 .north (-4, -3) (-29, -28) = true := by
  decide +kernel

end LangtonsAnt
