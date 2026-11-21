import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1567 : checkSingleBlackFast (-33, -13) 21121 .east (11, -8) (-36, -4) = true := by
  decide +kernel

end LangtonsAnt
