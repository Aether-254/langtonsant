import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1234 : checkSingleBlackFast (8, 21) 10207 .east (-6, -7) (-26, -6) = true := by
  decide +kernel

end LangtonsAnt
