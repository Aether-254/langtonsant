import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0851 : checkSingleBlackFast (-8, 10) 21390 .south (-5, -5) (-28, -20) = true := by
  decide +kernel

end LangtonsAnt
