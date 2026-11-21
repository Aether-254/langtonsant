import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0163 : checkSingleBlackFast (-2, 7) 1867 .east (3, -5) (-10, -7) = true := by
  decide +kernel

end LangtonsAnt
