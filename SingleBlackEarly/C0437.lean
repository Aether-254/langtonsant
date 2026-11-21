import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0437 : checkSingleBlackFast (16, 6) 8348 .north (-9, -1) (-23, -11) = true := by
  decide +kernel

end LangtonsAnt
