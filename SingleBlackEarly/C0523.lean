import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0523 : checkSingleBlackFast (-5, -8) 5781 .west (-15, -4) (-14, -16) = true := by
  decide +kernel

end LangtonsAnt
