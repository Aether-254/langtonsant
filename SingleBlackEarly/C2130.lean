import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2130 : checkSingleBlackFast (-85, -60) 22207 .east (45, 24) (-1, -63) = true := by
  decide +kernel

end LangtonsAnt
