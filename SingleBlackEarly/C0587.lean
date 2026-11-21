import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0587 : checkSingleBlackFast (21, 6) 9413 .east (-6, -4) (-24, -17) = true := by
  decide +kernel

end LangtonsAnt
