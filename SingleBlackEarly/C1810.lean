import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1810 : checkSingleBlackFast (-56, -35) 19405 .east (19, 9) (3, -42) = true := by
  decide +kernel

end LangtonsAnt
