import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0935 : checkSingleBlackFast (-13, 10) 7904 .north (-1, -1) (-23, 3) = true := by
  decide +kernel

end LangtonsAnt
