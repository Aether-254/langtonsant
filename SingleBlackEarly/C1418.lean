import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1418 : checkSingleBlackFast (-18, 2) 26158 .north (4, -7) (-39, -18) = true := by
  decide +kernel

end LangtonsAnt
