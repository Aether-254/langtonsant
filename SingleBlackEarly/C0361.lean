import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0361 : checkSingleBlackFast (13, -1) 3293 .west (-11, 2) (-14, -12) = true := by
  decide +kernel

end LangtonsAnt
