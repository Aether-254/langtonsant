import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1403 : checkSingleBlackFast (-21, 7) 11215 .east (-2, -7) (-26, -18) = true := by
  decide +kernel

end LangtonsAnt
