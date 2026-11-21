import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0299 : checkSingleBlackFast (7, 12) 7339 .east (5, -4) (-15, -17) = true := by
  decide +kernel

end LangtonsAnt
