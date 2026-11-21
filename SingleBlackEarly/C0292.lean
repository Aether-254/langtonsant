import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0292 : checkSingleBlackFast (12, 12) 4195 .east (1, -10) (-15, -13) = true := by
  decide +kernel

end LangtonsAnt
