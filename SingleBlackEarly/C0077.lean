import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0077 : checkSingleBlackFast (3, -6) 5673 .west (-15, -4) (-14, -16) = true := by
  decide +kernel

end LangtonsAnt
