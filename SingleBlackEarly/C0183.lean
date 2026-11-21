import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0183 : checkSingleBlackFast (9, -2) 1967 .east (1, -4) (-9, -7) = true := by
  decide +kernel

end LangtonsAnt
