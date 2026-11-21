import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1476 : checkSingleBlackFast (-27, -4) 24900 .north (6, 9) (-8, -39) = true := by
  decide +kernel

end LangtonsAnt
