import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1430 : checkSingleBlackFast (-22, 2) 33440 .north (-2, 8) (-16, -40) = true := by
  decide +kernel

end LangtonsAnt
