import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0263 : checkSingleBlackFast (11, 12) 2493 .east (-4, -11) (-15, -3) = true := by
  decide +kernel

end LangtonsAnt
