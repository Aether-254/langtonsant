import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1541 : checkSingleBlackFast (-32, -10) 25911 .east (6, -9) (-4, -36) = true := by
  decide +kernel

end LangtonsAnt
