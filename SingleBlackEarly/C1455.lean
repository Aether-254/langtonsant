import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1455 : checkSingleBlackFast (-25, -1) 11687 .east (1, -4) (-23, -9) = true := by
  decide +kernel

end LangtonsAnt
