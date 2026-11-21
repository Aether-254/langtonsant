import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2087 : checkSingleBlackFast2 (-82, -57) 19059 .east (29, 32) (7, -49) = true := by
  decide +kernel

end LangtonsAnt
