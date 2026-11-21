import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0313 : checkSingleBlackFast (1, 10) 2903 .west (-3, 4) (-15, -7) = true := by
  decide +kernel

end LangtonsAnt
