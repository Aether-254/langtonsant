import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1389 : checkSingleBlackFast2 (-19, 5) 16427 .west (-7, 7) (-30, -7) = true := by
  decide +kernel

end LangtonsAnt
