import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0250 : checkSingleBlackFast (13, 5) 2314 .south (-11, -8) (-16, -7) = true := by
  decide +kernel

end LangtonsAnt
