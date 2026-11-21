import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0184 : checkSingleBlackFast (9, -3) 1991 .east (1, -4) (-9, -7) = true := by
  decide +kernel

end LangtonsAnt
