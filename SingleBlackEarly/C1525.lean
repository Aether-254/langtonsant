import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1525 : checkSingleBlackFast (-28, -9) 19256 .north (16, 12) (-42, -4) = true := by
  decide +kernel

end LangtonsAnt
