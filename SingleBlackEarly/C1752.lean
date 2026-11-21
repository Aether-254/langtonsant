import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1752 : checkSingleBlackFast2 (-52, -24) 16681 .west (19, 25) (-45, 2) = true := by
  decide +kernel

end LangtonsAnt
