import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0207 : checkSingleBlackFast (8, 5) 4567 .east (-1, -8) (-15, -11) = true := by
  decide +kernel

end LangtonsAnt
