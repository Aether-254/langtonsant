import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2003 : checkSingleBlackFast2 (-74, -52) 19651 .east (27, 21) (-6, -39) = true := by
  decide +kernel

end LangtonsAnt
