import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1667 : checkSingleBlackFast (-45, -17) 27908 .north (11, 16) (-13, -42) = true := by
  decide +kernel

end LangtonsAnt
