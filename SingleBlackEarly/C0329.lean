import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0329 : checkSingleBlackFast (-4, 9) 2899 .west (-3, 4) (-15, -7) = true := by
  decide +kernel

end LangtonsAnt
