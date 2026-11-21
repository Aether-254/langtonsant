import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1471 : checkSingleBlackFast (-26, -1) 12440 .north (0, 9) (0, -25) = true := by
  decide +kernel

end LangtonsAnt
