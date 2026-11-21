import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0016 : checkSingleBlackFast (0, -3) 23018 .south (6, 0) (-23, -29) = true := by
  decide +kernel

end LangtonsAnt
