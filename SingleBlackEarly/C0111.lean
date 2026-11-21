import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0111 : checkSingleBlackFast (4, 1) 1631 .west (-2, 3) (-10, -6) = true := by
  decide +kernel

end LangtonsAnt
