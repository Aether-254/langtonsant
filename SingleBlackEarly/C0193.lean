import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0193 : checkSingleBlackFast (9, 1) 1703 .east (2, -4) (-9, -6) = true := by
  decide +kernel

end LangtonsAnt
