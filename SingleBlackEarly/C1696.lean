import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1696 : checkSingleBlackFast2 (-47, -24) 18917 .east (21, 6) (-2, -40) = true := by
  decide +kernel

end LangtonsAnt
