import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1962 : checkSingleBlackFast2 (-69, -48) 15274 .north (28, 16) (-55, -27) = true := by
  decide +kernel

end LangtonsAnt
