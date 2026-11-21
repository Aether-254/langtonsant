import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0598 : checkSingleBlackFast (20, 15) 7719 .east (-9, -4) (-23, -1) = true := by
  decide +kernel

end LangtonsAnt
