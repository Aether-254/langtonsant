import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0412 : checkSingleBlackFast (17, -4) 3727 .east (-3, -6) (-15, -11) = true := by
  decide +kernel

end LangtonsAnt
