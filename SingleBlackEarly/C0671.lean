import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0671 : checkSingleBlackFast (15, -11) 10272 .north (0, -2) (-24, 0) = true := by
  decide +kernel

end LangtonsAnt
