import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0121 : checkSingleBlackFast (5, 6) 5515 .west (-6, -1) (-18, -16) = true := by
  decide +kernel

end LangtonsAnt
