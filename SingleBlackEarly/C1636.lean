import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1636 : checkSingleBlackFast (-38, -20) 27419 .east (22, 10) (-19, -32) = true := by
  decide +kernel

end LangtonsAnt
