import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1013 : checkSingleBlackFast (-12, 8) 10075 .east (-2, -2) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
