import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0225 : checkSingleBlackFast (9, 10) 3701 .east (0, -8) (-14, -11) = true := by
  decide +kernel

end LangtonsAnt
