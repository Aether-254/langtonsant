import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0073 : checkSingleBlackFast (3, -5) 2177 .west (2, 5) (-13, -3) = true := by
  decide +kernel

end LangtonsAnt
