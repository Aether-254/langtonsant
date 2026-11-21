import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1866 : checkSingleBlackFast (-61, -36) 20959 .east (33, 12) (-13, -51) = true := by
  decide +kernel

end LangtonsAnt
