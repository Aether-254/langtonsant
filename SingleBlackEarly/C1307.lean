import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1307 : checkSingleBlackFast (-8, 16) 11516 .north (-1, -3) (-25, -1) = true := by
  decide +kernel

end LangtonsAnt
