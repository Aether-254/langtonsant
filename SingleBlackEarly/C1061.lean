import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1061 : checkSingleBlackFast (-14, -2) 10344 .north (2, -2) (-26, -4) = true := by
  decide +kernel

end LangtonsAnt
