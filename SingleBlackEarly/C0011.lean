import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0011 : checkSingleBlackFast (-3, -2) 777 .west (0, 4) (-8, -3) = true := by
  decide +kernel

end LangtonsAnt
