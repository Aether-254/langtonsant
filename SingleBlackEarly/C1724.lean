import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1724 : checkSingleBlackFast (-46, -28) 27835 .east (26, 14) (-15, -36) = true := by
  decide +kernel

end LangtonsAnt
