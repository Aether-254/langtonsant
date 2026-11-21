import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0271 : checkSingleBlackFast (14, 4) 4375 .east (-7, -10) (-13, -3) = true := by
  decide +kernel

end LangtonsAnt
