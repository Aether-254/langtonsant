import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1381 : checkSingleBlackFast (-19, 9) 11487 .east (2, -5) (-24, -24) = true := by
  decide +kernel

end LangtonsAnt
