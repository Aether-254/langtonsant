import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1075 : checkSingleBlackFast (-15, -6) 10532 .north (0, 0) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
