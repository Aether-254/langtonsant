import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0857 : checkSingleBlackFast (-10, 7) 10590 .north (0, 0) (-27, -1) = true := by
  decide +kernel

end LangtonsAnt
