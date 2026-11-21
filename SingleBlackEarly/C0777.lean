import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0777 : checkSingleBlackFast (24, -15) 10292 .north (0, -1) (-24, 1) = true := by
  decide +kernel

end LangtonsAnt
