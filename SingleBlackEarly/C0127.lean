import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0127 : checkSingleBlackFast (4, 6) 2277 .west (-5, 2) (-10, -10) = true := by
  decide +kernel

end LangtonsAnt
