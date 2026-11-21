import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0871 : checkSingleBlackFast (-8, 0) 10351 .west (-4, 7) (-26, -6) = true := by
  decide +kernel

end LangtonsAnt
