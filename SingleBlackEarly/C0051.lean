import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0051 : checkSingleBlackFast (2, -2) 3140 .south (-5, -3) (-13, -11) = true := by
  decide +kernel

end LangtonsAnt
