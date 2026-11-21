import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1778 : checkSingleBlackFast (-53, -28) 20543 .east (29, 8) (-17, -47) = true := by
  decide +kernel

end LangtonsAnt
