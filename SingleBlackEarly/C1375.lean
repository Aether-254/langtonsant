import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1375 : checkSingleBlackFast (-16, 9) 12023 .east (0, -7) (-26, -16) = true := by
  decide +kernel

end LangtonsAnt
