import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1187 : checkSingleBlackFast (25, 2) 10436 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
