import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1082 : checkSingleBlackFast (-9, -7) 10352 .north (0, -1) (-24, 1) = true := by
  decide +kernel

end LangtonsAnt
