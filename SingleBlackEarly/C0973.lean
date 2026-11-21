import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0973 : checkSingleBlackFast (3, 16) 9883 .east (-6, -5) (-24, -4) = true := by
  decide +kernel

end LangtonsAnt
