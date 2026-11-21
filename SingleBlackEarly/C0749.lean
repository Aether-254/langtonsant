import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0749 : checkSingleBlackFast (22, -12) 14523 .east (-7, 2) (-23, -23) = true := by
  decide +kernel

end LangtonsAnt
