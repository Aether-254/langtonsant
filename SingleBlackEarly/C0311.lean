import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0311 : checkSingleBlackFast (4, 10) 2887 .west (-4, 4) (-15, -6) = true := by
  decide +kernel

end LangtonsAnt
