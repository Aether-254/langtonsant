import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0442 : checkSingleBlackFast (15, 6) 20925 .east (-3, -7) (-33, -10) = true := by
  decide +kernel

end LangtonsAnt
