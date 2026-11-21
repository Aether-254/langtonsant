import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0119 : checkSingleBlackFast (7, 6) 2746 .south (-6, -6) (-13, -9) = true := by
  decide +kernel

end LangtonsAnt
