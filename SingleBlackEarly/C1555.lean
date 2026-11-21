import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1555 : checkSingleBlackFast (-34, -8) 11276 .north (6, 0) (-32, -12) = true := by
  decide +kernel

end LangtonsAnt
