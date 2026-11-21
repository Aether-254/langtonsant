import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0104 : checkSingleBlackFast2 (-4, 4) 10694 .south (1, -6) (-20, -19) = true := by
  decide +kernel

end LangtonsAnt
