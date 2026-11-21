import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1511 : checkSingleBlackFast (-30, -4) 11068 .north (4, 0) (-30, -8) = true := by
  decide +kernel

end LangtonsAnt
