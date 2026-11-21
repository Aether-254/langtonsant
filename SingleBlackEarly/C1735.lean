import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1735 : checkSingleBlackFast2 (-50, -25) 17395 .east (13, 16) (-9, -33) = true := by
  decide +kernel

end LangtonsAnt
