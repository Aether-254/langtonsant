import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0172 : checkSingleBlackFast (-6, 6) 9769 .east (-6, -3) (-23, -17) = true := by
  decide +kernel

end LangtonsAnt
