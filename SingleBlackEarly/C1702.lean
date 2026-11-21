import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1702 : checkSingleBlackFast (-44, -26) 27731 .east (25, 13) (-16, -35) = true := by
  decide +kernel

end LangtonsAnt
