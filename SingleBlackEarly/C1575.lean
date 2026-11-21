import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1575 : checkSingleBlackFast (-36, -9) 11264 .north (6, 0) (-32, -12) = true := by
  decide +kernel

end LangtonsAnt
