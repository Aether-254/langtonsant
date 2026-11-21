import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1505 : checkSingleBlackFast (-27, -8) 24013 .east (1, -7) (-13, -30) = true := by
  decide +kernel

end LangtonsAnt
