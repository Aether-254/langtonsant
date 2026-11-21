import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0936 : checkSingleBlackFast (-8, 12) 24398 .north (0, -6) (-33, -13) = true := by
  decide +kernel

end LangtonsAnt
