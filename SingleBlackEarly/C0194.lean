import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0194 : checkSingleBlackFast (10, 1) 6207 .west (-4, 4) (-21, -6) = true := by
  decide +kernel

end LangtonsAnt
