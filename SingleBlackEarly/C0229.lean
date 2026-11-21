import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0229 : checkSingleBlackFast (6, 9) 2191 .east (-1, -5) (-8, -9) = true := by
  decide +kernel

end LangtonsAnt
