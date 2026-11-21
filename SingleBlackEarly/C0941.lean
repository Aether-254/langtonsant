import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0941 : checkSingleBlackFast (22, 7) 11473 .west (-11, 5) (-23, -20) = true := by
  decide +kernel

end LangtonsAnt
