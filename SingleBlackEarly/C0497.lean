import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0497 : checkSingleBlackFast (0, 16) 9819 .west (-9, 7) (-24, -7) = true := by
  decide +kernel

end LangtonsAnt
