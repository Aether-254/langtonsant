import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1579 : checkSingleBlackFast (-37, -9) 30219 .east (6, -13) (-34, -2) = true := by
  decide +kernel

end LangtonsAnt
