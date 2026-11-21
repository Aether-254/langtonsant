import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1512 : checkSingleBlackFast2 (-31, -4) 18722 .north (1, -6) (-34, -13) = true := by
  decide +kernel

end LangtonsAnt
