import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1821 : checkSingleBlackFast (-59, -31) 24697 .east (25, 13) (3, -48) = true := by
  decide +kernel

end LangtonsAnt
