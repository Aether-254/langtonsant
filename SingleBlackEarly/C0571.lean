import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0571 : checkSingleBlackFast (19, -2) 10508 .south (-12, 1) (-26, -7) = true := by
  decide +kernel

end LangtonsAnt
