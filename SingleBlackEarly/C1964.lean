import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1964 : checkSingleBlackFast (-70, -49) 20133 .east (26, 16) (10, -49) = true := by
  decide +kernel

end LangtonsAnt
