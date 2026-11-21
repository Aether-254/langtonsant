import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1111 : checkSingleBlackFast (-1, -11) 10476 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
