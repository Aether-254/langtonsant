import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0116 : checkSingleBlackFast (6, 5) 1771 .east (3, -6) (-9, -7) = true := by
  decide +kernel

end LangtonsAnt
