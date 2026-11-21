import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1741 : checkSingleBlackFast (-51, -27) 13951 .west (12, 23) (-42, 4) = true := by
  decide +kernel

end LangtonsAnt
