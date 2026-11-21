import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0963 : checkSingleBlackFast (5, 17) 9579 .east (-6, -4) (-23, -6) = true := by
  decide +kernel

end LangtonsAnt
