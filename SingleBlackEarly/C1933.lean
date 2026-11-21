import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1933 : checkSingleBlackFast2 (-68, -43) 18331 .east (22, 25) (0, -42) = true := by
  decide +kernel

end LangtonsAnt
