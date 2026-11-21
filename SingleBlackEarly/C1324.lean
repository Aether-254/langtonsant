import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1324 : checkSingleBlackFast (-13, 17) 22156 .north (-4, -2) (-4, -36) = true := by
  decide +kernel

end LangtonsAnt
