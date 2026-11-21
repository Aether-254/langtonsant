import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0977 : checkSingleBlackFast (1, 17) 7827 .east (-6, -6) (-21, -10) = true := by
  decide +kernel

end LangtonsAnt
