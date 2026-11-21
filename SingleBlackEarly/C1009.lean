import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1009 : checkSingleBlackFast (-14, 7) 9623 .east (-2, -2) (-21, -20) = true := by
  decide +kernel

end LangtonsAnt
