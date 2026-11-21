import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1291 : checkSingleBlackFast (-3, 22) 11100 .north (-1, -3) (-25, -1) = true := by
  decide +kernel

end LangtonsAnt
