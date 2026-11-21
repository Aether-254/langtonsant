import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0334 : checkSingleBlackFast (4, 13) 9485 .east (-6, -11) (-23, -9) = true := by
  decide +kernel

end LangtonsAnt
