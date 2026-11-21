import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1290 : checkSingleBlackFast2 (-4, 22) 11847 .east (-6, -11) (-30, -10) = true := by
  decide +kernel

end LangtonsAnt
