import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0651 : checkSingleBlackFast (10, -11) 9504 .north (0, -1) (-24, 1) = true := by
  decide +kernel

end LangtonsAnt
