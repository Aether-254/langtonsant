import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0307 : checkSingleBlackFast (6, 13) 3275 .west (-3, 2) (-17, -7) = true := by
  decide +kernel

end LangtonsAnt
