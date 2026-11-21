import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1276 : checkSingleBlackFast (1, 21) 10404 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
