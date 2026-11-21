import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0402 : checkSingleBlackFast (13, -5) 2707 .west (-8, 2) (-13, -10) = true := by
  decide +kernel

end LangtonsAnt
