import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0759 : checkSingleBlackFast (19, -15) 10304 .north (0, -1) (-24, 1) = true := by
  decide +kernel

end LangtonsAnt
