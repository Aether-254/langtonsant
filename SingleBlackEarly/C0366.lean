import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0366 : checkSingleBlackFast (12, 2) 6145 .east (-4, -11) (-19, -5) = true := by
  decide +kernel

end LangtonsAnt
