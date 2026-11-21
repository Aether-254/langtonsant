import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1424 : checkSingleBlackFast (-23, 4) 22888 .north (-2, 4) (-4, -32) = true := by
  decide +kernel

end LangtonsAnt
