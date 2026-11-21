import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1535 : checkSingleBlackFast (-33, -5) 28328 .north (4, 10) (-8, -36) = true := by
  decide +kernel

end LangtonsAnt
