import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0069 : checkSingleBlackFast (-2, -6) 23554 .south (-17, -5) (-36, -2) = true := by
  decide +kernel

end LangtonsAnt
