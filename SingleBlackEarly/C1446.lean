import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1446 : checkSingleBlackFast (-25, 2) 23484 .north (-2, -6) (-22, -24) = true := by
  decide +kernel

end LangtonsAnt
