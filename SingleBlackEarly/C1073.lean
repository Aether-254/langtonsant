import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1073 : checkSingleBlackFast (-14, -5) 10540 .north (0, 0) (-26, 0) = true := by
  decide +kernel

end LangtonsAnt
