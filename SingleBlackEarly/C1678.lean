import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1678 : checkSingleBlackFast (-44, -23) 24053 .east (10, -3) (3, -39) = true := by
  decide +kernel

end LangtonsAnt
