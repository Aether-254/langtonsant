import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0377 : checkSingleBlackFast (15, -3) 14965 .east (-13, -12) (-26, -8) = true := by
  decide +kernel

end LangtonsAnt
