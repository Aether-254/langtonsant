import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0214 : checkSingleBlackFast (9, 7) 6541 .east (-2, -9) (-15, -15) = true := by
  decide +kernel

end LangtonsAnt
