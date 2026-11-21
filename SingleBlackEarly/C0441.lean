import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0441 : checkSingleBlackFast (15, 5) 33328 .south (-14, -2) (-14, -34) = true := by
  decide +kernel

end LangtonsAnt
