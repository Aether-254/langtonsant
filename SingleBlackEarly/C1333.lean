import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1333 : checkSingleBlackFast (-16, 15) 13159 .east (0, -5) (-24, -22) = true := by
  decide +kernel

end LangtonsAnt
