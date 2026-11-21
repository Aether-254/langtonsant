import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0562 : checkSingleBlackFast (20, -6) 4987 .west (-14, 4) (-17, -16) = true := by
  decide +kernel

end LangtonsAnt
