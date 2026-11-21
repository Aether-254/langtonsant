import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0129 : checkSingleBlackFast (5, 1) 6443 .east (-3, -6) (-7, -19) = true := by
  decide +kernel

end LangtonsAnt
