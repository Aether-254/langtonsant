import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1331 : checkSingleBlackFast (-15, 17) 11543 .east (1, -5) (-24, -23) = true := by
  decide +kernel

end LangtonsAnt
