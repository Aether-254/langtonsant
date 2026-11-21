import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0028 : checkSingleBlackFast (1, 2) 5193 .east (-6, -14) (-18, -11) = true := by
  decide +kernel

end LangtonsAnt
