import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1030 : checkSingleBlackFast2 (-6, 17) 10859 .east (3, -8) (-23, -23) = true := by
  decide +kernel

end LangtonsAnt
