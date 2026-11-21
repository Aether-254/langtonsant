import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0567 : checkSingleBlackFast (20, -3) 6772 .south (-13, 0) (-23, -2) = true := by
  decide +kernel

end LangtonsAnt
