import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1221 : checkSingleBlackFast (10, 16) 12611 .east (-7, -1) (-20, -23) = true := by
  decide +kernel

end LangtonsAnt
