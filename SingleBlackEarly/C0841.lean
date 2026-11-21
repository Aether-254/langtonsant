import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0841 : checkSingleBlackFast (-1, 16) 11270 .north (-2, -1) (-25, -4) = true := by
  decide +kernel

end LangtonsAnt
