import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0274 : checkSingleBlackFast (15, 8) 20367 .east (5, -5) (-28, -29) = true := by
  decide +kernel

end LangtonsAnt
