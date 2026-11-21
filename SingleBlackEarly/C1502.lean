import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1502 : checkSingleBlackFast (-28, -7) 24332 .north (0, 6) (-8, -36) = true := by
  decide +kernel

end LangtonsAnt
