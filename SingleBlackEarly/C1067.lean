import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1067 : checkSingleBlackFast (-14, -3) 10256 .north (0, -2) (-24, -10) = true := by
  decide +kernel

end LangtonsAnt
