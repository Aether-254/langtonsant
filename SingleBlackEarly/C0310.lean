import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0310 : checkSingleBlackFast (4, 12) 2959 .west (-3, 4) (-15, -7) = true := by
  decide +kernel

end LangtonsAnt
