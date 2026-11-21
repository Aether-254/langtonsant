import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0461 : checkSingleBlackFast (19, 11) 12283 .east (-9, -7) (-24, -7) = true := by
  decide +kernel

end LangtonsAnt
