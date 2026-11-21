import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0797 : checkSingleBlackFast (25, -6) 13066 .north (-4, 3) (-25, -16) = true := by
  decide +kernel

end LangtonsAnt
