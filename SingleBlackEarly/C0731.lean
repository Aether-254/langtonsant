import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0731 : checkSingleBlackFast (12, -13) 11140 .north (0, -1) (-24, 1) = true := by
  decide +kernel

end LangtonsAnt
