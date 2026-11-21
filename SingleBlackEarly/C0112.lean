import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0112 : checkSingleBlackFast (4, 0) 1191 .east (5, -6) (-9, -5) = true := by
  decide +kernel

end LangtonsAnt
