import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0431 : checkSingleBlackFast (19, 4) 8181 .east (-1, -10) (-22, -16) = true := by
  decide +kernel

end LangtonsAnt
