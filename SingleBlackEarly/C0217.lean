import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0217 : checkSingleBlackFast (10, 8) 3267 .east (-3, -7) (-6, -11) = true := by
  decide +kernel

end LangtonsAnt
