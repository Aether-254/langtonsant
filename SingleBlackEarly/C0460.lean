import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0460 : checkSingleBlackFast (19, 12) 8992 .south (-12, -4) (-16, -18) = true := by
  decide +kernel

end LangtonsAnt
