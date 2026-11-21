import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0370 : checkSingleBlackFast (13, -3) 3555 .east (-1, -6) (-15, -9) = true := by
  decide +kernel

end LangtonsAnt
