import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0533 : checkSingleBlackFast (2, -8) 6943 .east (-2, -4) (-13, -14) = true := by
  decide +kernel

end LangtonsAnt
