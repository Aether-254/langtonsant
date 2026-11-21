import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1386 : checkSingleBlackFast2 (-18, 6) 15444 .north (-7, 3) (-1, -25) = true := by
  decide +kernel

end LangtonsAnt
