import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1510 : checkSingleBlackFast (-30, -2) 35492 .north (8, 10) (-6, -38) = true := by
  decide +kernel

end LangtonsAnt
