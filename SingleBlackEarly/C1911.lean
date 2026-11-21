import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1911 : checkSingleBlackFast2 (-66, -41) 18227 .east (21, 24) (-1, -41) = true := by
  decide +kernel

end LangtonsAnt
