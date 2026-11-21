import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0109 : checkSingleBlackFast (-6, 4) 1461 .east (7, -5) (-9, -6) = true := by
  decide +kernel

end LangtonsAnt
