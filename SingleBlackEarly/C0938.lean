import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0938 : checkSingleBlackFast (-8, 14) 7883 .east (-1, -4) (-19, -19) = true := by
  decide +kernel

end LangtonsAnt
