import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2012 : checkSingleBlackFast2 (-72, -52) 16652 .north (31, 21) (-57, -37) = true := by
  decide +kernel

end LangtonsAnt
