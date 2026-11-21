import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1955 : checkSingleBlackFast2 (-70, -45) 18435 .east (23, 26) (1, -43) = true := by
  decide +kernel

end LangtonsAnt
