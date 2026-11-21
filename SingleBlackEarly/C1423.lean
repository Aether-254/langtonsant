import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1423 : checkSingleBlackFast (-22, 4) 21488 .north (-2, -7) (-32, -11) = true := by
  decide +kernel

end LangtonsAnt
