import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1668 : checkSingleBlackFast (-43, -18) 20023 .east (24, 3) (-22, -42) = true := by
  decide +kernel

end LangtonsAnt
