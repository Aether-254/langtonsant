import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0488 : checkSingleBlackFast (5, 15) 5575 .west (-7, 0) (-19, -3) = true := by
  decide +kernel

end LangtonsAnt
