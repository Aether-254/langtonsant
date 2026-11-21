import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2065 : checkSingleBlackFast2 (-80, -55) 18955 .east (28, 31) (6, -48) = true := by
  decide +kernel

end LangtonsAnt
