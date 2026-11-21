import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2135 : checkSingleBlackFast (-86, -64) 20275 .east (33, 27) (0, -45) = true := by
  decide +kernel

end LangtonsAnt
