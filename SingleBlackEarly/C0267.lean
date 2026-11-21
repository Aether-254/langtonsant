import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0267 : checkSingleBlackFast (12, 7) 28563 .east (-7, -12) (-15, -29) = true := by
  decide +kernel

end LangtonsAnt
