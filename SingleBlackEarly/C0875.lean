import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0875 : checkSingleBlackFast (-10, 2) 6682 .north (-1, 1) (-22, -6) = true := by
  decide +kernel

end LangtonsAnt
