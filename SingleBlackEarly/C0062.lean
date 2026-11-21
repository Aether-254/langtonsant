import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0062 : checkSingleBlackFast (-4, -4) 1347 .west (0, 7) (-10, -4) = true := by
  decide +kernel

end LangtonsAnt
