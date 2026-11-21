import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0364 : checkSingleBlackFast (14, 0) 9450 .south (-9, -6) (-24, -15) = true := by
  decide +kernel

end LangtonsAnt
