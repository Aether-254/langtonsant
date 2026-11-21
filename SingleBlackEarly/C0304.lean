import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0304 : checkSingleBlackFast (6, 12) 9289 .east (0, -4) (-10, -19) = true := by
  decide +kernel

end LangtonsAnt
