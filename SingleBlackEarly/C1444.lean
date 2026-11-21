import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1444 : checkSingleBlackFast (-24, 4) 24392 .south (-1, -8) (-37, -4) = true := by
  decide +kernel

end LangtonsAnt
