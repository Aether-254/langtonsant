import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1450 : checkSingleBlackFast (-23, -1) 22700 .south (-5, -8) (-13, -22) = true := by
  decide +kernel

end LangtonsAnt
