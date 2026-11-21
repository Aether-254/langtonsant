import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1448 : checkSingleBlackFast (-23, 2) 25920 .north (-2, -6) (-22, -24) = true := by
  decide +kernel

end LangtonsAnt
