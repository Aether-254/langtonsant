import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0088 : checkSingleBlackFast (4, 4) 1303 .east (0, -7) (-10, -4) = true := by
  decide +kernel

end LangtonsAnt
