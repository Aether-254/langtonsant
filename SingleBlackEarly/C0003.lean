import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0003 : checkSingleBlackFast (0, -1) 10415 .west (0, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
