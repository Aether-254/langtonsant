import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1569 : checkSingleBlackFast (-32, -13) 19464 .north (18, 14) (-44, -6) = true := by
  decide +kernel

end LangtonsAnt
