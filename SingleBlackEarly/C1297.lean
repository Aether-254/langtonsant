import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1297 : checkSingleBlackFast (-8, 21) 14051 .east (-1, -11) (-30, -11) = true := by
  decide +kernel

end LangtonsAnt
