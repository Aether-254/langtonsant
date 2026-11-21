import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0153 : checkSingleBlackFast (-1, 5) 5133 .east (12, 2) (-8, -15) = true := by
  decide +kernel

end LangtonsAnt
