import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0976 : checkSingleBlackFast (2, 19) 9568 .north (0, -4) (-24, -2) = true := by
  decide +kernel

end LangtonsAnt
