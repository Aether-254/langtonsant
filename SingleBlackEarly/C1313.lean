import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1313 : checkSingleBlackFast (-10, 16) 12330 .north (1, -3) (-28, 2) = true := by
  decide +kernel

end LangtonsAnt
