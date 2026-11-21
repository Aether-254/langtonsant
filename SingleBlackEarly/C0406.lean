import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0406 : checkSingleBlackFast (15, -7) 6562 .south (-11, -2) (-24, 1) = true := by
  decide +kernel

end LangtonsAnt
