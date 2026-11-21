import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1833 : checkSingleBlackFast (-56, -37) 20712 .north (30, 26) (-56, -18) = true := by
  decide +kernel

end LangtonsAnt
