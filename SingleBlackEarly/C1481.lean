import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1481 : checkSingleBlackFast (-24, -5) 28040 .south (2, -6) (-38, -4) = true := by
  decide +kernel

end LangtonsAnt
