import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2175 : checkSingleBlackFast2 (-90, -65) 19475 .east (33, 36) (11, -53) = true := by
  decide +kernel

end LangtonsAnt
