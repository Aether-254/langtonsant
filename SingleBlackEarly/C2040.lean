import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2040 : checkSingleBlackFast (-79, -52) 19770 .north (31, 24) (-58, -37) = true := by
  decide +kernel

end LangtonsAnt
