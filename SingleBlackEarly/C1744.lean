import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1744 : checkSingleBlackFast2 (-50, -29) 19093 .east (16, 6) (0, -39) = true := by
  decide +kernel

end LangtonsAnt
