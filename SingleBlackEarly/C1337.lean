import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1337 : checkSingleBlackFast (-15, 14) 11668 .north (-1, -1) (-25, 1) = true := by
  decide +kernel

end LangtonsAnt
